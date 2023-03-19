use proc_macro::Span;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

use crate::production::{
  Grammar, Production, ProductionRef, ProductionRule, ProductionRuleRef, Terminal,
};
use crate::util::{ParseError, ParseResult};

pub enum FirstCacheState {
  Hit(HashSet<Terminal>),
  // The terminals for this state are currently being calculated.
  Pending,
}

/// A cache of the sets of possible first elements seen in a production rule,
/// given the production's name.
pub type ProductionFirstTable = HashMap<ProductionRuleRef, FirstCacheState>;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProductionInst {
  // A reference to a particular instance of a rule.
  pub rule_ref: ProductionRuleRef,
}

impl ProductionInst {
  pub fn new(rule_ref: ProductionRuleRef) -> Self {
    Self { rule_ref }
  }

  pub fn from_production(production: &Rc<Production>) -> Vec<Self> {
    production
      .rules
      .iter()
      .enumerate()
      .map(|(idx, _rules)| {
        Self::new(ProductionRef::new(Rc::downgrade(&production)).rule_ref(idx as u32))
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
      match first_cache.get(&self.rule_ref) {
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
          first_cache.insert(self.rule_ref.clone(), FirstCacheState::Pending);
        }
      }
    }

    let rules = self.rule_ref.rules();
    debug_assert!(rules.len() >= pos);
    let mut terms = HashSet::new();

    match rules.rule_at(pos) {
      Some(ProductionRule::Intermediate(production_ref)) => {
        let production = production_ref.deref();
        let prod_insts = Self::from_production(&production);
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
        terms.insert(Terminal::Epsilon(Span::call_site().into()));
      }
    }

    // Insert the computed next symbols into the first_cache if we just
    // calculated the first set for this production instance in its first form
    // (i.e. pos == 0).
    if pos == 0 {
      // Insert into the cache if it doesn't already exist.
      if let Some(state) = first_cache.get(&self.rule_ref) {
        match &state {
          FirstCacheState::Pending => {
            first_cache.insert(self.rule_ref.clone(), FirstCacheState::Hit(terms.clone()));
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
    if pos != rules.len() && terms.remove(&Terminal::Epsilon(Span::call_site().into())) {
      terms.extend(self.calculate_first_set(pos + 1, first_cache));
    }

    return terms;
  }
}

/// A partial production state is a production state that hasn't finalized its
/// list of possible_lookaheads. The only difference between this struct and
/// `ProductionState` is that this ignores `possible_lookaheads` for equality
/// comparison and hash calculation.
#[derive(Clone)]
struct PartialProductionState {
  inst: ProductionInst,
  // Ranges from [0, rules.len()], and is the position of the dot.
  pos: u32,
  // The list of possible tokens that can follow this rule.
  possible_lookaheads: BTreeSet<Terminal>,
}

impl<'a> PartialProductionState {
  pub fn new<I: Iterator<Item = Terminal>>(inst: ProductionInst, possible_lookaheads: I) -> Self {
    Self {
      inst,
      pos: 0,
      possible_lookaheads: possible_lookaheads.collect(),
    }
  }

  pub fn merge_lookaheads<I: Iterator<Item = Terminal>>(&mut self, lookaheads: I) {
    self.possible_lookaheads.extend(lookaheads)
  }

  fn from_production<I: Iterator<Item = Terminal>>(
    prod_ptr: &Rc<Production>,
    possible_lookaheads: I,
  ) -> Vec<Self> {
    let lookaheads = possible_lookaheads.collect::<Vec<_>>();
    ProductionInst::from_production(prod_ptr)
      .into_iter()
      .map(|inst| Self::new(inst, lookaheads.clone().into_iter()))
      .collect()
  }

  pub fn is_complete(&self) -> bool {
    self.pos == self.inst.rule_ref.rules().len()
  }

  // Returns the next symbol in this production, if there are any symbols left.
  pub fn next_sym(&self) -> Option<&ProductionRule> {
    if self.is_complete() {
      return None;
    }

    return self.inst.rule_ref.rules().rule_at(self.pos);
  }
}

impl From<ProductionState> for PartialProductionState {
  fn from(prod_state: ProductionState) -> Self {
    Self {
      inst: prod_state.inst,
      pos: prod_state.pos,
      possible_lookaheads: prod_state.possible_lookaheads,
    }
  }
}

impl Hash for PartialProductionState {
  fn hash<H: Hasher>(&self, state: &mut H) {
    // Production states are grouped into equivalence classes based only on
    // their name and position, not lookaheads.
    self.inst.hash(state);
    self.pos.hash(state);
  }
}

impl PartialEq for PartialProductionState {
  fn eq(&self, other: &Self) -> bool {
    self.inst == other.inst && self.pos == other.pos
  }
}

impl Eq for PartialProductionState {}

impl PartialOrd for PartialProductionState {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self
      .inst
      .partial_cmp(&other.inst)
      .and_then(|cmp| Some(cmp.then(self.pos.partial_cmp(&other.pos)?)))
  }
}

impl Ord for PartialProductionState {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.inst.cmp(&other.inst).then(self.pos.cmp(&other.pos))
  }
}

impl Display for PartialProductionState {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    let prod_state: ProductionState = self.clone().into();
    write!(f, "{}", prod_state)
  }
}

/// A production state is an instance of a production and how far through the
/// production we've parsed so far (represented by a dot).
///
/// i.e. `A -> b . C d`
/// indicates that b has already been parsed, and we're ready to parse C d.
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProductionState {
  pub inst: ProductionInst,
  // Ranges from [0, rules.len()], and is the position of the dot.
  pub pos: u32,
  // The list of possible tokens that can follow this rule.
  pub possible_lookaheads: BTreeSet<Terminal>,
}

impl ProductionState {
  pub fn new<I: Iterator<Item = Terminal>>(inst: ProductionInst, possible_lookaheads: I) -> Self {
    Self {
      inst,
      pos: 0,
      possible_lookaheads: possible_lookaheads.collect(),
    }
  }

  pub fn is_complete(&self) -> bool {
    self.pos == self.inst.rule_ref.rules().len()
  }

  /// Returns the next symbol in this production, if there are any symbols left.
  pub fn next_sym(&self) -> Option<&ProductionRule> {
    if self.is_complete() {
      return None;
    }

    return self.inst.rule_ref.rules().rule_at(self.pos);
  }

  /// Advances the production state to the next token.
  pub fn advance(&self) -> Self {
    debug_assert!(!self.is_complete());
    Self {
      pos: self.pos + 1,
      ..self.clone()
    }
  }

  pub fn prev_sym(&self) -> Option<&ProductionRule> {
    if self.pos == 0 {
      None
    } else {
      Some(&self.inst.rule_ref.rules().rules[self.pos as usize - 1])
    }
  }
}

impl From<PartialProductionState> for ProductionState {
  fn from(partial_prod_state: PartialProductionState) -> Self {
    Self {
      inst: partial_prod_state.inst,
      pos: partial_prod_state.pos,
      possible_lookaheads: partial_prod_state.possible_lookaheads,
    }
  }
}

impl Display for ProductionState {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    let mut rule_strs: Vec<_> = self
      .inst
      .rule_ref
      .rules()
      .rules
      .iter()
      .map(|rule| format!("{}", rule))
      .collect();
    rule_strs.insert(self.pos as usize, ".".to_string());

    write!(
      f,
      "[<{}> => {}, {}]",
      self.inst.rule_ref.name(),
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct LRStateBuilder {
  pub states: BTreeSet<ProductionState>,
}

impl LRStateBuilder {
  fn new() -> Self {
    Self {
      states: BTreeSet::new(),
    }
  }

  fn insert(&mut self, state: ProductionState) -> bool {
    self.states.insert(state)
  }
}

impl Display for LRStateBuilder {
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

#[derive(PartialEq, Eq)]
enum ActionBuilder {
  Shift(LRStateBuilder),
  Reduce(ProductionRuleRef),
}

impl Display for ActionBuilder {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      ActionBuilder::Shift(prod_states) => {
        write!(
          f,
          "shift({})",
          prod_states
            .states
            .iter()
            .map(|prod_state| prod_state.to_string())
            .collect::<Vec<_>>()
            .join(", ")
        )
      }
      ActionBuilder::Reduce(prod_rule_ref) => {
        write!(f, "reduce({})", prod_rule_ref)
      }
    }
  }
}

// type TransitionSet = HashMap<Action, Rc<LRState>>;
struct TransitionSetBuilder {
  action_map: HashMap<Terminal, ActionBuilder>,
  goto_map: HashMap<ProductionRef, LRStateBuilder>,
}

impl TransitionSetBuilder {
  fn new() -> Self {
    Self {
      action_map: HashMap::new(),
      goto_map: HashMap::new(),
    }
  }

  fn insert_shift(&mut self, term: Terminal, prod_state: ProductionState) -> ParseResult {
    match self.action_map.get_mut(&term) {
      Some(ActionBuilder::Shift(lr_state)) => {
        lr_state.insert(prod_state);
        Ok(())
      }
      Some(ActionBuilder::Reduce(prod_ref)) => ParseError::new(
        &format!(
          "Shift/reduce conflict for rules {} (shift) and {} (reduce)",
          prod_state.inst.rule_ref, prod_ref
        ),
        prod_state.inst.rule_ref.span(),
      )
      .into(),
      None => {
        let mut lr_state = LRStateBuilder::new();
        lr_state.insert(prod_state);
        self.action_map.insert(term, ActionBuilder::Shift(lr_state));
        Ok(())
      }
    }
  }

  fn insert_reduce(&mut self, term: Terminal, prod_rule_ref: ProductionRuleRef) -> ParseResult {
    match self.action_map.get_mut(&term) {
      Some(action @ ActionBuilder::Shift(_)) => ParseError::new(
        &format!(
          "Shift/reduce conflict for rules {} (shift) and {} (reduce)",
          action, prod_rule_ref
        ),
        prod_rule_ref.span(),
      )
      .into(),
      Some(ActionBuilder::Reduce(other_prod_rule_ref)) => ParseError::new(
        &format!(
          "Reduce/reduce conflict for rules {} and {}",
          prod_rule_ref, other_prod_rule_ref
        ),
        prod_rule_ref.span(),
      )
      .into(),
      None => {
        self
          .action_map
          .insert(term, ActionBuilder::Reduce(prod_rule_ref));
        Ok(())
      }
    }
  }

  fn insert_goto(&mut self, prod_ref: ProductionRef, prod_state: ProductionState) -> ParseResult {
    match self.goto_map.get_mut(&prod_ref) {
      Some(lr_state) => {
        lr_state.insert(prod_state);
        Ok(())
      }
      None => {
        let mut lr_state = LRStateBuilder::new();
        lr_state.insert(prod_state);
        self.goto_map.insert(prod_ref, lr_state);
        Ok(())
      }
    }
  }
}

impl Display for TransitionSetBuilder {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    let mut was_prev = false;
    for (term, action) in &self.action_map {
      if !was_prev {
        write!(f, "\n")?;
      } else {
        was_prev = true;
      }
      write!(f, "{} => {}", term, action)?;
    }
    for (prod_ref, prod_refs) in &self.goto_map {
      if !was_prev {
        write!(f, "\n")?;
      } else {
        was_prev = true;
      }
      write!(
        f,
        "{} => {}",
        prod_ref,
        prod_refs
          .states
          .iter()
          .map(|prod_ref| prod_ref.to_string())
          .collect::<Vec<_>>()
          .join(", ")
      )?;
    }

    Ok(())
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
  /// List all derivative states from this one via application of production
  /// rules to nonterminal symbols immediately following "pos".
  fn from_lr_states(
    lr_state_builder: &LRStateBuilder,
    first_cache: &mut ProductionFirstTable,
  ) -> Self {
    let mut queue: VecDeque<PartialProductionState> = VecDeque::new();
    let mut expanded_rules: HashSet<PartialProductionState> = HashSet::new();

    queue.extend(
      lr_state_builder
        .states
        .iter()
        .cloned()
        .map(|state| state.into()),
    );

    // TODO fix closure calc: missing lookaheads for recursive rules for some reason.
    while let Some(state) = queue.pop_front() {
      if let Some(mut prod_state) = expanded_rules.take(&state) {
        // If this rule has already been expanded, we just need to merge
        // the possible lookaheads discovered from this expansion.
        prod_state.merge_lookaheads(state.possible_lookaheads.clone().into_iter());
        expanded_rules.insert(prod_state);

        // Don't re-expand the next symbol of this rule.
        continue;
      }

      // If the rule wasn't found in the map, we need to add it and expand the
      // next symbol if it is a production.
      expanded_rules.insert(state.clone());

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
            if next_terms.remove(&Terminal::Epsilon(Span::call_site().into())) {
              next_terms.extend(state.possible_lookaheads.clone());
            }

            let prod_states =
              PartialProductionState::from_production(&prod, next_terms.into_iter());
            queue.extend(prod_states);
          }
          _ => {}
        }
      }
    }
    // for prod in &expanded_rules {
    //   eprintln!("prod: {}", prod);
    // }

    return Self {
      states: expanded_rules
        .into_iter()
        .map(|rule| rule.into())
        .collect::<Vec<_>>(),
    };
  }

  /// Computes the set of actions that can be taken from this state, and the
  /// list of production states that each action would yield.
  fn transitions(&self) -> ParseResult<TransitionSetBuilder> {
    let mut transitions = TransitionSetBuilder::new();

    for state in &self.states {
      if state.is_complete() {
        // Completed states can be reduced.
        for term in &state.possible_lookaheads {
          transitions.insert_reduce(term.clone(), state.inst.rule_ref.clone())?;
        }

        continue;
      }

      match state.next_sym() {
        Some(ProductionRule::Intermediate(intermediate)) => {
          transitions.insert_goto(intermediate.clone(), state.advance())?;
        }
        Some(ProductionRule::Terminal(term)) => {
          transitions.insert_shift(term.clone(), state.advance())?;
        }
        None => unreachable!(),
      }
    }

    // eprintln!("{}", transitions);

    Ok(transitions)
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

pub enum LRTableEntry {
  Resolved(LRState),
  Unresolved(LRStateBuilder),
}

impl LRTableEntry {
  pub fn lr_state(&self) -> &LRState {
    match self {
      LRTableEntry::Resolved(lr_state) => lr_state,
      LRTableEntry::Unresolved(_) => unreachable!(),
    }
  }

  pub fn state_builder_ref(&self) -> &LRStateBuilder {
    match self {
      LRTableEntry::Resolved(lr_state) => &lr_state.states,
      LRTableEntry::Unresolved(lr_state_builder) => lr_state_builder,
    }
  }

  pub fn as_parent_set(lr_entry_ptr: &Rc<LRTableEntry>) -> HashSet<Rc<LRTableEntry>> {
    let mut parent_set = HashSet::new();
    parent_set.insert(lr_entry_ptr.clone());
    return parent_set;
  }
}

impl From<LRStateBuilder> for LRTableEntry {
  fn from(lr_state_builder: LRStateBuilder) -> Self {
    Self::Unresolved(lr_state_builder)
  }
}

impl Hash for LRTableEntry {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.state_builder_ref().hash(state);
  }
}

impl PartialEq for LRTableEntry {
  fn eq(&self, other: &Self) -> bool {
    self.state_builder_ref() == other.state_builder_ref()
  }
}

impl Eq for LRTableEntry {}

impl Display for LRTableEntry {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      LRTableEntry::Resolved(lr_state) => write!(f, "{}", lr_state),
      LRTableEntry::Unresolved(lr_state_builder) => write!(f, "unresolved({})", lr_state_builder),
    }
  }
}

#[derive(PartialEq, Eq)]
pub enum Action {
  Shift(Rc<LRTableEntry>),
  Reduce(ProductionRuleRef),
}

impl Display for Action {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      Action::Shift(lr_table_entry) => write!(
        f,
        "shift({})",
        match lr_table_entry.deref() {
          LRTableEntry::Resolved(lr_state) => {
            lr_state
              .states
              .states
              .iter()
              .map(|state| format!("{}", state))
              .collect::<Vec<_>>()
              .join(", ")
          }
          _ => unreachable!(),
        }
      ),
      Action::Reduce(prod_rule_ref) => write!(f, "reduce({})", prod_rule_ref.name()),
    }
  }
}

pub struct TransitionSet {
  pub action_map: HashMap<Terminal, Action>,
  pub goto_map: HashMap<ProductionRef, Rc<LRTableEntry>>,
}

impl TransitionSet {
  fn new() -> Self {
    Self {
      action_map: HashMap::new(),
      goto_map: HashMap::new(),
    }
  }
}

impl Display for TransitionSet {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    let mut first = true;
    for (term, action) in &self.action_map {
      if !first {
        write!(f, "\n")?;
      }
      first = false;
      write!(f, "{} -> {}", term, action)?;
    }
    for (prod_ref, lr_table_entry) in &self.goto_map {
      if !first {
        write!(f, "\n")?;
      }
      first = false;
      write!(
        f,
        "<{}> -> goto({})",
        prod_ref.name(),
        match lr_table_entry.deref() {
          LRTableEntry::Resolved(lr_state) => {
            lr_state
              .states
              .states
              .iter()
              .map(|state| format!("{}", state))
              .collect::<Vec<_>>()
              .join(", ")
          }
          _ => unreachable!(),
        }
      )?;
    }

    Ok(())
  }
}

pub struct LRState {
  pub states: LRStateBuilder,
  pub transitions: TransitionSet,
  pub parent_states: HashSet<Rc<LRTableEntry>>,
  pub uid: u64,
}

impl LRState {
  pub fn new<I: Iterator<Item = ProductionState>>(
    states: I,
    transitions: TransitionSet,
    parent_states: HashSet<Rc<LRTableEntry>>,
    uid: u64,
  ) -> Self {
    Self {
      states: LRStateBuilder {
        states: states.collect(),
      },
      transitions,
      parent_states,
      uid,
    }
  }

  pub fn parents_of(lr_states: &HashSet<Rc<LRTableEntry>>) -> HashSet<Rc<LRTableEntry>> {
    lr_states
      .iter()
      .fold(HashSet::new(), |mut parent_states, lr_state| {
        parent_states.extend(lr_state.lr_state().parent_states.clone());
        parent_states
      })
  }

  pub fn last_sym(&self) -> Option<&ProductionRule> {
    let repr_state = self.states.states.iter().next().unwrap();
    repr_state.prev_sym()
  }

  pub fn is_initial_state(&self) -> bool {
    self.parent_states.is_empty()
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
    write!(f, "{}\n{}", self.states, self.transitions)
  }
}

pub struct LRTable {
  pub states: HashSet<Rc<LRTableEntry>>,
  pub initial_state: Rc<LRTableEntry>,
}

impl LRTable {
  fn calculate_transitions(
    states: &mut HashSet<Rc<LRTableEntry>>,
    first_table: &mut ProductionFirstTable,
    lr_state_builder: &LRStateBuilder,
    parent_lr_state: Option<Rc<LRTableEntry>>,
    next_uid: &mut u64,
  ) -> ParseResult<Rc<LRTableEntry>> {
    let lr_table_entry = LRTableEntry::from(lr_state_builder.clone());
    if let Some(prior_lr_state) = states.get(&lr_table_entry) {
      return Ok(prior_lr_state.clone());
    }
    if states.len() % 100 == 0 {
      eprintln!("states: {}", states.len());
    }
    // eprintln!("line: {}", lr_state_builder);

    let lr_state = Rc::new(lr_table_entry);
    assert!(states.insert(lr_state.clone()));

    let closure = Closure::from_lr_states(lr_state_builder, first_table);
    // eprintln!("\tclozure: {}", closure);
    let transitions = closure.transitions()?;

    let mut transition_set = TransitionSet::new();

    for (term, action_builder) in transitions.action_map {
      match action_builder {
        ActionBuilder::Reduce(prod_ref) => {
          transition_set
            .action_map
            .insert(term.clone(), Action::Reduce(prod_ref));
        }
        ActionBuilder::Shift(lr_state_builder) => {
          let child_lr_state = Self::calculate_transitions(
            states,
            first_table,
            &lr_state_builder,
            Some(lr_state.clone()),
            next_uid,
          )?;
          transition_set
            .action_map
            .insert(term.clone(), Action::Shift(child_lr_state));
        }
      }
    }

    for (prod_ref, lr_state_builder) in transitions.goto_map {
      let child_lr_state = Self::calculate_transitions(
        states,
        first_table,
        &lr_state_builder,
        Some(lr_state.clone()),
        next_uid,
      )?;
      transition_set.goto_map.insert(prod_ref, child_lr_state);
    }

    let mut lr_state = states.take(&lr_state).unwrap();
    if let LRTableEntry::Unresolved(lr_state_builder) = lr_state.deref() {
      let mut parent_states = HashSet::new();
      if let Some(parent_state) = parent_lr_state {
        parent_states.insert(parent_state);
      }
      unsafe {
        *Rc::get_mut_unchecked(&mut lr_state) = LRTableEntry::Resolved(LRState::new(
          lr_state_builder.states.clone().into_iter(),
          transition_set,
          parent_states,
          *next_uid,
        ));
      }
      *next_uid += 1;
      states.insert(lr_state.clone());
    } else {
      return ParseError::new("Unexpected resolved LR table entry", Span::call_site()).into();
    }
    return Ok(lr_state);
  }

  pub fn from_grammar(grammar: &Grammar) -> ParseResult<Self> {
    let init_state_ptr = grammar.starting_rule();

    let mut initial_lr_state = LRStateBuilder::new();
    (0..init_state_ptr.deref().rules().len()).for_each(|idx| {
      initial_lr_state.insert(ProductionState::new(
        ProductionInst::new(init_state_ptr.rule_ref(idx as u32)),
        vec![Terminal::EndOfStream(Span::call_site().into())].into_iter(),
      ));
    });

    let mut states = HashSet::new();
    let mut first_table = ProductionFirstTable::new();
    let mut next_uid = 0u64;

    let initial_state = Self::calculate_transitions(
      &mut states,
      &mut first_table,
      &initial_lr_state,
      None,
      &mut next_uid,
    )?;

    Ok(Self {
      states,
      initial_state,
    })
  }
}

impl Display for LRTable {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for state in self.states.iter() {
      write!(f, "state {}: {}\n", state.lr_state().uid, state)?;
    }
    Ok(())
  }
}
