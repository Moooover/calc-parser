use proc_macro::Span;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::rc::{Rc, Weak};

use crate::production::{
  Grammar, Production, ProductionName, ProductionRule, ProductionRules, Terminal,
};

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
  // The index of this rule in the list of possible expansions of a rule. Used
  // only to uniquely identify rule instances.
  rule_idx: u32,
}

impl ProductionInst {
  pub fn new(name: &ProductionName, rules: &ProductionRules, rule_idx: u32) -> Self {
    Self {
      name: name.clone(),
      rules: rules.clone(),
      rule_idx,
    }
  }

  pub fn from_production(production: &Production) -> Vec<Self> {
    production
      .rules
      .iter()
      .enumerate()
      .map(|(idx, rules)| Self {
        name: production.name.clone(),
        rules: rules.clone(),
        rule_idx: idx as u32,
      })
      .collect()
  }

  /// Returns the list of possible next terminals that this rule could match
  /// after `pos` rules have already been matched. May include epsilon, which
  /// means the rule is skippable.
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
        let prod_insts = Self::from_production(production);
        terms.extend(prod_insts.iter().fold(HashSet::new(), |mut terms, inst| {
          terms.extend(inst.calculate_first_set(0, first_cache));
          terms
        }));
      }
      Some(ProductionRule::Terminal(terminal)) => {
        terms.insert(terminal.clone());
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
      } else {
        debug_assert!(false, "Expected state to be pending in the cache.");
      }
    }

    // If terms includes epsilon, we have to include all possible first
    // symbols of the advanced production state. The terminal's span isn't
    // used in equality comparison, so it can be set to anything.
    // Only do this if this rule isn't complete yet. Otherwise, the presence of
    // epsilon means that this rule is skippable from this point, and therefore
    // the lookahead terminals are also possible first token.
    if pos != self.rules.len() && terms.remove(&Terminal::Epsilon(Span::call_site())) {
      terms.extend(self.calculate_first_set(pos + 1, first_cache));
    }

    return terms;
  }
}

impl Hash for ProductionInst {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
    self.rule_idx.hash(state);
  }
}

impl PartialEq for ProductionInst {
  fn eq(&self, other: &Self) -> bool {
    self.name == other.name && self.rule_idx == other.rule_idx
  }
}

impl Eq for ProductionInst {}

impl PartialOrd for ProductionInst {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self
      .name
      .partial_cmp(&other.name)
      .and_then(|cmp| Some(cmp.then(self.rule_idx.partial_cmp(&other.rule_idx)?)))
  }
}

impl Ord for ProductionInst {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self
      .name
      .cmp(&other.name)
      .then(self.rule_idx.cmp(&other.rule_idx))
  }
}

/// A production state is an instance of a production and how far through the
/// production we've parsed so far (represented by a dot).
///
/// i.e. `A -> b . C d`
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
    let mut rule_strs: Vec<_> = self
      .inst
      .rules
      .rules
      .iter()
      .map(|rule| format!("{}", rule))
      .collect();
    rule_strs.insert(self.pos as usize, ".".to_string());

    write!(
      f,
      "[<{}> => {}, {}]",
      self.inst.name.name(),
      rule_strs.join(" "),
      &self
        .possible_lookaheads
        .iter()
        .map(|sym| format!("{}", sym))
        .collect::<Vec<_>>()
        .join("/")
    )
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

impl Display for Action {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      Action::Reduce(production_ptr) => {
        write!(
          f,
          "reduce({})",
          production_ptr.upgrade().unwrap().name.name()
        )
      }
      Action::Shift(terminal) => {
        write!(f, "shift({})", terminal)
      }
    }
  }
}

// struct Transition {
//   action: Action,
//   next_state: ProductionState,
// }

type TransitionSet = HashMap<Action, Rc<LRState>>;

/// A state in the parsing DFA, which contains the set of all possible
/// productions that we could currently be parsing. Note that these rules must
/// be compatible with each other, meaning they have all the same tokens before
/// the '.'.
struct Closure {
  states: Vec<ProductionState>,
}

impl Closure {
  /// List all derivative states from this one via application of production
  /// rules to nonterminal symbols immediately following "pos".
  fn from_lr_states(states: &Vec<ProductionState>, first_cache: &mut ProductionFirstTable) -> Self {
    let mut queue: VecDeque<ProductionState> = VecDeque::new();
    let mut expanded_rules: HashMap<ProductionName, Vec<ProductionState>> = HashMap::new();
    // let mut closure = Vec::new();

    queue.extend(states.iter().map(|state| state.clone()));

    while let Some(state) = queue.pop_front() {
      if !state.is_complete() {
        match state.next_sym() {
          Some(ProductionRule::Intermediate(production)) => {
            let prod = production.deref();
            // Don't expand rules that have already been expanded, or recursive
            // references to this rule.
            // if prod.name != state.inst.name && !expanded_rules.contains(&prod.name) {
            let mut next_terms = state.inst.calculate_first_set(state.pos + 1, first_cache);

            // If next_terms includes epsilon, the rest of this state is
            // skippable, so include possible_lookaheads.
            if next_terms.remove(&Terminal::Epsilon(Span::call_site())) {
              next_terms.extend(state.possible_lookaheads.clone());
            }

            if let Some(prod_state) = expanded_rules.get_mut(&prod.name) {
            } else {
              let prod_states = ProductionState::from_production(
                prod.deref().clone(),
                next_terms.into_iter().collect(),
              );
              queue.extend(prod_states.into_iter());
            }
          }
          _ => {}
        }
      }

      match expanded_rules.get_mut(&state.inst.name) {
        Some(rules) => {
          rules.push(state);
        }
        None => {
          expanded_rules.insert(state.inst.name.clone(), vec![state]);
        }
      }
    }

    return Self {
      states: expanded_rules.into_values().collect::<Vec<_>>().concat(),
    };
  }

  /// Computes the set of actions that can be taken from this state, and the
  /// list of production states that each action would yield.
  fn transitions(&self) -> HashMap<Action, Vec<ProductionState>> {
    let mut transitions: HashMap<Action, Vec<ProductionState>> = HashMap::new();
    eprintln!("{}", self);

    for state in &self.states {
      if state.is_complete() {
        // Completed states don't have any transitions.
        continue;
      }

      let action = match state.next_sym() {
        Some(ProductionRule::Intermediate(intermediate)) => {
          Action::Reduce(intermediate.deref_weak())
        }
        Some(ProductionRule::Terminal(term)) => Action::Shift(term.clone()),
        None => unreachable!(),
      };

      match transitions.get_mut(&action) {
        Some(lr_state) => {
          lr_state.push(state.advance());
        }
        None => {
          transitions.insert(action, vec![state.advance()]);
        }
      }
    }

    for (action, prod_states) in &transitions {
      eprintln!(
        "transz: {} -> {}",
        action,
        prod_states
          .iter()
          .map(|state| format!("{}", state))
          .collect::<Vec<_>>()
          .join(", ")
      );
    }

    transitions
  }
}

impl Display for Closure {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for (i, state) in self.states.iter().enumerate() {
      if i != 0 {
        write!(f, ", ")?;
      }
      write!(f, "{}", state)?;
    }
    Ok(())
  }
}

struct LRState {
  states: BTreeSet<ProductionState>,
  transitions: Option<TransitionSet>,
}

impl LRState {
  pub fn new<I: Iterator<Item = ProductionState>>(states: I) -> Self {
    Self {
      states: states.collect(),
      transitions: None,
    }
  }

  fn set_transitions(&mut self, transitions: TransitionSet) {
    self.transitions = Some(transitions);
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
      if i != 0 {
        write!(f, ", ")?;
      }
      write!(f, "{}", state)?;
    }
    Ok(())
  }
}

pub struct LRTable {
  states: HashSet<Rc<LRState>>,
  first_table: ProductionFirstTable,
  initial_state: Option<Rc<LRState>>,
}

impl LRTable {
  pub fn new() -> Self {
    LRTable {
      states: HashSet::new(),
      first_table: HashMap::new(),
      initial_state: None,
    }
  }

  fn calculate_transitions(&mut self, prod_states: &Vec<ProductionState>) -> Rc<LRState> {
    let lr_state = LRState::new(prod_states.clone().into_iter());
    if let Some(lr_state) = self.states.get(&lr_state) {
      return lr_state.clone();
    }

    let lr_state = Rc::new(lr_state);
    self.states.insert(lr_state);

    let closure = Closure::from_lr_states(prod_states, &mut self.first_table);
    eprintln!("{}", closure);
    let transitions = closure.transitions();
    let mut transition_set = TransitionSet::new();

    for (action, prod_states) in transitions.into_iter() {
      let child_lr_state = self.calculate_transitions(&prod_states);
      transition_set.insert(action, child_lr_state);
    }

    // TODO mutate this in place with RefCell.
    let mut lr_state = LRState::new(prod_states.clone().into_iter());
    lr_state.set_transitions(transition_set);
    let lr_state = Rc::new(lr_state);
    return lr_state;
  }

  pub fn from_grammar(grammar: &Grammar) -> Self {
    let mut table = LRTable::new();

    let init_state_ptr = grammar.starting_rule();
    let init_state = init_state_ptr.deref();
    let initial_lr_state = init_state
      .rules()
      .iter()
      .map(|rule| {
        ProductionState::new(
          ProductionInst::new(&init_state.name, &rule, 0),
          vec![Terminal::EndOfStream(Span::call_site())],
        )
      })
      .collect();
    let initial_state = table.calculate_transitions(&initial_lr_state);
    table.initial_state = Some(initial_state);

    return table;
  }
}

impl Display for LRTable {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for state in self.states.iter() {
      write!(f, "{}\n", state)?;
    }
    Ok(())
  }
}
