use proc_macro::Span;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::{Rc, Weak};

use crate::production::{
  Production, ProductionName, ProductionRefT, ProductionRule, ProductionRules, Terminal,
};

use crate::production::Grammar;

enum FirstCacheState {
  Hit(HashSet<Terminal>),
  // The terminals for this state are currently being calculated.
  Pending,
}

/// A cache of the sets of possible first elements seen in a production rule,
/// given the production's name.
type ProductionFirstTable = HashMap<ProductionName, FirstCacheState>;

#[derive(Clone)]
struct ProductionInst {
  // The name of the production, i.e. the LHS of A -> b C d ...
  name: ProductionName,
  // The rules that make up this production, i.e. the RHS.
  rules: ProductionRules,
}

impl ProductionInst {
  pub fn new(name: &ProductionName, rules: &ProductionRules) -> Self {
    Self {
      name: name.clone(),
      rules: rules.clone(),
    }
  }

  pub fn from_production(production: &Production) -> Vec<Self> {
    production
      .rules
      .iter()
      .map(|rules| Self {
        name: production.name.clone(),
        rules: rules.clone(),
      })
      .collect()
  }

  pub fn calculate_first_set(
    &self,
    pos: u32,
    first_cache: &mut ProductionFirstTable,
  ) -> HashSet<Terminal> {
    if pos == 0 {
      match first_cache.get(&self.name) {
        Some(FirstCacheState::Hit(terms)) => {
          return terms.clone();
        }
        Some(FirstCacheState::Pending) => {
          // If this production is in a pending state, that means some
          // recursive parent caller is calculating this state, so ignore more
          // instances of the same state.
          return HashSet::new();
        }
        None => {
          // Set the cache state to pending.
          first_cache.insert(self.name.clone(), FirstCacheState::Pending);
        }
      }
    }

    debug_assert!(self.rules.rules.len() >= pos as usize);
    let mut terms = HashSet::new();

    match self.rules.rule_at(pos) {
      Some(ProductionRule::Intermediate(production_ref)) => {
        let prod_ptr = production_ref.deref();
        let production: &Production = prod_ptr.deref();
        // calculate_first_set doesn't ever use possible_lookaheads, so we can
        // set it to the empty set.
        let prod_insts = Self::from_production(production);
        terms.extend(prod_insts.iter().fold(HashSet::new(), |mut terms, inst| {
          terms.extend(inst.calculate_first_set(0, first_cache));
          terms
        }));

        // If terms includes epsilon, we have to include all possible first
        // symbols of the advanced production state. The terminal's span isn't
        // used in equality comparison, so it can be set to anything.
        if terms.remove(&Terminal::Epsilon(Span::call_site())) {
          terms.extend(self.calculate_first_set(pos + 1, first_cache));
        }
      }
      Some(ProductionRule::Terminal(terminal)) => {
        if let Terminal::Epsilon(_) = terminal {
          terms.extend(self.calculate_first_set(pos + 1, first_cache));
        } else {
          terms.insert(terminal.clone());
        }
      }
      // If the production is finished, return epsilon. This epsilon was not
      // defined explicitly in the macro, so its span is the call site.
      None => {
        terms.insert(Terminal::Epsilon(Span::call_site()));
      }
    }

    // Insert the computed next symbols into the first_cache if we just
    // calculated the first set for this production instance in its first form
    // (i.e. pos == 0).
    if pos == 0 {
      // Insert into the cache if it doesn't already exist.
      if let Some(state) = first_cache.get(&self.name) {
        match &state {
          FirstCacheState::Pending => {
            first_cache.insert(self.name.clone(), FirstCacheState::Hit(terms.clone()));
          }
          _ => {}
        }
      }
    }

    return terms;
  }
}

impl Hash for ProductionInst {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
  }
}

impl PartialEq for ProductionInst {
  fn eq(&self, other: &Self) -> bool {
    self.name == other.name
  }
}

impl Eq for ProductionInst {}

impl PartialOrd for ProductionInst {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.name.partial_cmp(&other.name)
  }
}

impl Ord for ProductionInst {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.name.cmp(&other.name)
  }
}

/// A production state is an instance of a production and how far through the
/// production we've parsed so far (represented by a dot).
///
/// i.e. A -> b . C d
/// indicates that b has already been parsed, and we're ready to parse C d.
#[derive(Clone)]
struct ProductionState {
  inst: ProductionInst,
  // Ranges from [0, rules.len()], and is the position of the dot.
  pos: u32,
  // The list of possible tokens that can follow this rule.
  possible_lookaheads: Vec<Terminal>,
}

impl<'a> ProductionState {
  pub fn new(inst: ProductionInst, possible_lookaheads: Vec<Terminal>) -> Self {
    Self {
      inst,
      pos: 0,
      possible_lookaheads,
    }
  }

  fn from_production(production: &Production, possible_lookaheads: Vec<Terminal>) -> Vec<Self> {
    ProductionInst::from_production(production)
      .into_iter()
      .map(|inst| Self::new(inst, possible_lookaheads.clone()))
      .collect()
  }

  pub fn merge(&mut self, other: ProductionState) {
    debug_assert!(*self == other);
    self.possible_lookaheads.extend(other.possible_lookaheads)
  }

  pub fn is_complete(&self) -> bool {
    self.pos as usize == self.inst.rules.rules.len()
  }

  // Returns the next symbol in this production, if there are any symbols left.
  pub fn next_sym(&self) -> Option<&ProductionRule> {
    if self.is_complete() {
      return None;
    }

    return Some(&self.inst.rules.rules[self.pos as usize]);
  }

  pub fn advance(&self) -> ProductionState {
    debug_assert!((self.pos as usize) < self.inst.rules.rules.len());
    Self {
      pos: self.pos + 1,
      ..self.clone()
    }
  }
}

impl Hash for ProductionState {
  fn hash<H: Hasher>(&self, state: &mut H) {
    // Production states are grouped into equivalence classes based only on
    // their name and position, not lookaheads.
    self.inst.hash(state);
    self.pos.hash(state);
  }
}

impl PartialEq for ProductionState {
  fn eq(&self, other: &Self) -> bool {
    self.inst == other.inst && self.pos == other.pos
  }
}

impl Eq for ProductionState {}

impl PartialOrd for ProductionState {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self
      .inst
      .partial_cmp(&other.inst)
      .and_then(|cmp| Some(cmp.then(self.pos.partial_cmp(&other.pos)?)))
  }
}

impl Ord for ProductionState {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.inst.cmp(&other.inst).then(self.pos.cmp(&other.pos))
  }
}

impl Display for ProductionState {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(
      f,
      "[{} {}, {}]",
      self.inst.name,
      self.pos,
      &self
        .possible_lookaheads
        .iter()
        .fold("".to_string(), |s, sym| s + "/" + &format!("{}", sym))[1..]
    )
  }
}

/// A state in the parsing DFA, which contains the set of all possible
/// productions that we could currently be parsing. Note that these rules must
/// be compatible with each other, meaning they have all the same tokens before
/// the '.'.
struct Closure {
  states: Vec<ProductionState>,
}

impl Closure {
  // List all derivative states from this one via application of production
  // rules to nonterminal symbols immediately following "pos".
  fn from_lr_states(states: &Vec<ProductionState>, first_cache: &mut ProductionFirstTable) -> Self {
    let mut queue: VecDeque<ProductionState> = VecDeque::new();
    let mut closure = Vec::new();

    queue.extend(states.iter().map(|state| state.clone()));

    while let Some(state) = queue.pop_front() {
      if !state.is_complete() {
        match state.next_sym() {
          Some(ProductionRule::Intermediate(production)) => match &production.production {
            ProductionRefT::Resolved(prod_ptr) => {
              let prod = prod_ptr.upgrade().unwrap();
              let next_terms = state.inst.calculate_first_set(state.pos + 1, first_cache);
              let prod_states = ProductionState::from_production(
                prod.deref().clone(),
                next_terms.into_iter().collect(),
              );
              queue.extend(prod_states.into_iter());
            }
            _ => panic!("Unexpected unresolved intermediate"),
          },
          _ => {}
        }
      }
      closure.push(state);
    }

    return Self { states: closure };
  }
}

enum Action {
  Shift(Terminal),
  Reduce(Weak<Production>),
}

impl Hash for Action {
  fn hash<H: Hasher>(&self, state: &mut H) {
    match self {
      Action::Shift(terminal) => {
        state.write_u64(0);
        terminal.hash(state);
      }
      Action::Reduce(production_ptr) => {
        state.write_u64(1);
        production_ptr.upgrade().unwrap().name.hash(state);
      }
    };
  }
}

impl PartialEq for Action {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Action::Shift(terminal1), Action::Shift(terminal2)) => terminal1 == terminal2,
      (Action::Reduce(production_ptr1), Action::Reduce(production_ptr2)) => {
        production_ptr1.upgrade().unwrap().name == production_ptr2.upgrade().unwrap().name
      }
      _ => false,
    }
  }
}

impl Eq for Action {}

// struct Transition {
//   action: Action,
//   next_state: ProductionState,
// }

struct TransitionSet {
  // TODO figure out how to represent these, will need lookup on actions and
  // productionstates (for duplicate state checking)
  transitions: HashMap<Action, ProductionState>,
}

impl TransitionSet {
  pub fn new() -> Self {
    Self {
      transitions: HashMap::new(),
    }
  }

  pub fn add(&mut self, action: Action, next_state: ProductionState) {
    match self.transitions.get(&action) {
      Some(production_state) => {}
      None => {}
    }
  }
}

struct LRState {
  states: BTreeSet<ProductionState>,
  transitions: TransitionSet,
}

impl LRState {
  pub fn new<I: Iterator<Item = ProductionState>>(states: I, transitions: TransitionSet) -> Self {
    Self {
      states: states.collect(),
      transitions,
    }
  }
}

impl Hash for LRState {
  fn hash<H: Hasher>(&self, state: &mut H) {
    // Production states are grouped into equivalence classes based only on
    // their name and position, not lookaheads.
    self.states.hash(state);
  }
}

impl PartialEq for LRState {
  fn eq(&self, other: &Self) -> bool {
    self.states == other.states
  }
}

impl Eq for LRState {}

impl Display for LRState {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for (i, state) in self.states.iter().enumerate() {
      write!(f, "{}", state)?;
      if i != 0 {
        write!(f, ", ")?;
      }
    }
    Ok(())
  }
}

pub struct LRTable {
  states: HashSet<Rc<LRState>>,
  entries: HashMap<Action, Rc<LRState>>,
  first_table: ProductionFirstTable,
}

impl LRTable {
  pub fn new() -> Self {
    LRTable {
      states: HashSet::new(),
      entries: HashMap::new(),
      first_table: HashMap::new(),
    }
  }

  pub fn calculate_transitions(&mut self, states: &Vec<ProductionState>) -> TransitionSet {
    let trans_set = TransitionSet::new();

    let closure = Closure::from_lr_states(states, &mut self.first_table);
    self.states.insert(Rc::new(LRState::new(
      closure.states.into_iter(),
      TransitionSet::new(),
    )));

    trans_set
  }
}

impl From<Grammar> for LRTable {
  fn from(grammar: Grammar) -> Self {
    let mut table = LRTable::new();

    let init_state_ptr = grammar.starting_rule();
    let init_state = init_state_ptr.deref();
    let x = ProductionState::new(
      ProductionInst {
        name: init_state.name.clone(),
        rules: init_state.rules[0].clone(),
      },
      vec![Terminal::EndOfStream(Span::call_site())],
    );
    table.calculate_transitions(&vec![x]);

    return table;
  }
}

impl Display for LRTable {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for state in self.states.iter() {
      write!(f, "{} ", state)?;
    }
    Ok(())
  }
}
