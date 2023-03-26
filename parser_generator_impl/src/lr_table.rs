use proc_macro::Span;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
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

  /// Returns true if this state changed with this operation.
  fn merge_lookaheads<I: Iterator<Item = Terminal>>(&mut self, lookaheads: I) -> bool {
    let prev_n_possible_lookaheads = self.possible_lookaheads.len();
    self.possible_lookaheads.extend(lookaheads);
    prev_n_possible_lookaheads != self.possible_lookaheads.len()
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

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
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

  fn merge(&mut self, other: LRStateBuilder) {
    self.states.extend(other.states);
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
  Terminate(ProductionRuleRef),
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
      ActionBuilder::Terminate(prod_rule_ref) => {
        write!(f, "terminate({})", prod_rule_ref)
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
      Some(ActionBuilder::Terminate(prod_ref)) => ParseError::new(
        &format!(
          "Shift/reduce conflict for rules {} (shift) and {} (terminate)",
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
      Some(ActionBuilder::Terminate(other_prod_rule_ref)) => ParseError::new(
        &format!(
          "Reduce/reduce conflict for rules {} and {} (terminate)",
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

  fn insert_terminate(&mut self, term: Terminal, prod_rule_ref: ProductionRuleRef) -> ParseResult {
    match self.action_map.get_mut(&term) {
      Some(action @ ActionBuilder::Shift(_)) => ParseError::new(
        &format!(
          "Shift/reduce conflict for rules {} (shift) and {} (terminate)",
          action, prod_rule_ref
        ),
        prod_rule_ref.span(),
      )
      .into(),
      Some(ActionBuilder::Reduce(other_prod_rule_ref)) => ParseError::new(
        &format!(
          "Reduce/reduce conflict for rules {} (terminate) and {}",
          prod_rule_ref, other_prod_rule_ref
        ),
        prod_rule_ref.span(),
      )
      .into(),
      Some(ActionBuilder::Terminate(_)) => Ok(()),
      None => {
        self
          .action_map
          .insert(term, ActionBuilder::Terminate(prod_rule_ref));
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
    while let Some(mut state) = queue.pop_front() {
      if let Some(mut prod_state) = expanded_rules.take(&state) {
        // If this rule has already been expanded, we just need to merge
        // the possible lookaheads discovered from this expansion.
        if !prod_state.merge_lookaheads(state.possible_lookaheads.clone().into_iter()) {
          // If the state didn't change, we don't have to re-expand the next symbol.
          expanded_rules.insert(prod_state);
          continue;
        }

        state = prod_state;
      }

      // If the rule wasn't found in the map, we need to add it and expand the
      // next symbol if it is a production.
      expanded_rules.insert(state.clone());

      if !state.is_complete() {
        match state.next_sym() {
          Some(ProductionRule::Intermediate(production)) => {
            let prod = production.deref();
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

    return Self {
      states: expanded_rules
        .into_iter()
        .map(|rule| rule.into())
        .collect::<Vec<_>>(),
    };
  }

  /// Computes the set of actions that can be taken from this state, and the
  /// list of production states that each action would yield.
  fn transitions(&self, grammar: &Grammar) -> ParseResult<TransitionSetBuilder> {
    let mut transitions = TransitionSetBuilder::new();

    for state in &self.states {
      if state.is_complete() {
        // Completed states can be reduced.
        for term in &state.possible_lookaheads {
          if grammar.is_starting_rule(state.inst.rule_ref.prod_ref()) {
            transitions.insert_terminate(term.clone(), state.inst.rule_ref.clone())?;
          } else {
            transitions.insert_reduce(term.clone(), state.inst.rule_ref.clone())?;
          }
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

    // eprintln!("transitionz: {}", transitions);

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

#[derive(Clone)]
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

  fn lr_state_mut(&mut self) -> &mut LRState {
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

impl PartialOrd for LRTableEntry {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self
      .state_builder_ref()
      .partial_cmp(other.state_builder_ref())
  }
}

impl Ord for LRTableEntry {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.state_builder_ref().cmp(other.state_builder_ref())
  }
}

impl Display for LRTableEntry {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      LRTableEntry::Resolved(lr_state) => write!(f, "{}", lr_state),
      LRTableEntry::Unresolved(lr_state_builder) => write!(f, "unresolved({})", lr_state_builder),
    }
  }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action {
  Shift(Rc<LRTableEntry>),
  Reduce(ProductionRuleRef),
  Terminate(ProductionRuleRef),
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
      Action::Reduce(prod_rule_ref) => write!(
        f,
        "reduce({}:{})",
        prod_rule_ref.name(),
        prod_rule_ref.rule_idx()
      ),
      Action::Terminate(prod_rule_ref) => write!(
        f,
        "terminate({}:{})",
        prod_rule_ref.name(),
        prod_rule_ref.rule_idx()
      ),
    }
  }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TransitionSet {
  pub action_map: BTreeMap<Action, BTreeSet<Terminal>>,
  pub goto_map: BTreeMap<ProductionRef, Rc<LRTableEntry>>,
}

impl TransitionSet {
  fn new() -> Self {
    Self {
      action_map: BTreeMap::new(),
      goto_map: BTreeMap::new(),
    }
  }

  fn insert_action(&mut self, term: Terminal, action: Action) {
    if let Some(terminals) = self.action_map.get_mut(&action) {
      terminals.insert(term);
    } else {
      self.action_map.insert(action, BTreeSet::from([term]));
    }
  }

  fn update_refs(&mut self, ref_map: &mut StateMap) {
    let mut action_map: BTreeMap<Action, BTreeSet<Terminal>> = BTreeMap::new();
    self
      .action_map
      .clone()
      .into_iter()
      .for_each(|(action, terms)| {
        eprintln!("Remapping {}", action);
        let action = match action {
          Action::Shift(lr_table_entry) => Action::Shift(ref_map.remap(lr_table_entry)),
          action @ Action::Reduce(_) | action @ Action::Terminate(_) => action,
        };

        eprintln!("insert/remove");
        let terms = if let Some(mut other_terms) = action_map.remove(&action) {
          other_terms.extend(terms);
          other_terms
        } else {
          terms
        };
        action_map.insert(action, terms);
      });
    self.action_map = action_map;
    eprintln!("Remapping goto map");
    self.goto_map = self
      .goto_map
      .clone()
      .into_iter()
      .map(|(prod_ref, lr_table_entry)| (prod_ref, ref_map.remap(lr_table_entry)))
      .collect();
  }
}

impl Display for TransitionSet {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    let mut first = true;
    for (action, terms) in &self.action_map {
      if !first {
        write!(f, "\n")?;
      }
      first = false;
      write!(
        f,
        "({}) -> {}",
        terms
          .iter()
          .map(|term| format!("{}", term))
          .collect::<Vec<_>>()
          .join(", "),
        action
      )?;
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

#[derive(Clone)]
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

  fn add_parent(&mut self, parent: Rc<LRTableEntry>) {
    self.parent_states.insert(parent);
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

  /// Merges two lr states, assuming their transition sets are already identical.
  pub fn merge(&mut self, other: LRState) {
    self.states.merge(other.states);
    self.parent_states.extend(other.parent_states);
  }

  fn update_refs(&mut self, ref_map: &mut StateMap) {
    eprintln!("update parent state refs");
    self.parent_states = self
      .parent_states
      .clone()
      .into_iter()
      .map(|lr_table_entry| ref_map.remap(lr_table_entry))
      .collect();
    eprintln!("update transitions refs");
    self.transitions.update_refs(ref_map);
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

struct TransitionSet2 {
  transition_set: TransitionSet,
}

// impl TransitionSet2 {
//   fn merge(&mut self, other: TransitionSet2) {
//     // Only need to merge action_map, since goto_map must already be identical
//     // between two TransitionSets being merged.
//     other
//       .transition_set
//       .action_map
//       .into_iter()
//       .for_each(|(action, other_terms)| {
//         if let Some(terms) = self.action_map.get_mut(&action) {
//           terms.extend(other_terms);
//         } else {
//           self.action_map.insert(action, other_terms);
//         }
//       });
//     if self.transition_set.action_map.len() != other.transition_set.action_map.len() {
//       return false;
//     }

//     self
//       .transition_set
//       .action_map
//       .iter()
//       .zip(other.transition_set.action_map.iter())
//       .all(
//         |((action1, terms1), (action2, terms2))| match (action1, action2) {
//           (Action::Shift(lr_table_entry1), Action::Shift(lr_table_entry2)) => {
//             lr_table_entry1 == lr_table_entry2
//           }
//           (Action::Reduce(prod_rule_ref1), Action::Reduce(prod_rule_ref2)) => {
//             prod_rule_ref1.prod_ptr() == prod_rule_ref2.prod_ptr()
//               && prod_rule_ref1
//                 .rules()
//                 .construction_pattern_eq(prod_rule_ref2.rules())
//           }
//           (Action::Terminate(prod_rule_ref1), Action::Terminate(prod_rule_ref2)) => {
//             prod_rule_ref1.prod_ptr() == prod_rule_ref2.prod_ptr()
//               && prod_rule_ref1
//                 .rules()
//                 .construction_pattern_eq(prod_rule_ref2.rules())
//           }
//           _ => false,
//         } && terms1 == terms2,
//       )
//       eprintln!("New trans set: {}", self);
//   }
// }

impl From<TransitionSet> for TransitionSet2 {
  fn from(transition_set: TransitionSet) -> Self {
    Self { transition_set }
  }
}

impl Hash for TransitionSet2 {
  fn hash<H: Hasher>(&self, state: &mut H) {
    for (action, terms) in &self.transition_set.action_map {
      match action {
        Action::Shift(lr_table_entry) => {
          state.write_u64(0);
          lr_table_entry.hash(state);
        }
        Action::Reduce(prod_rule_ref) => {
          state.write_u64(1);
          prod_rule_ref.prod_ptr().hash(state);
          prod_rule_ref.rules().construction_pattern_hash(state);
        }
        Action::Terminate(prod_rule_ref) => {
          state.write_u64(2);
          prod_rule_ref.prod_ptr().hash(state);
          prod_rule_ref.rules().construction_pattern_hash(state);
        }
      }

      terms.hash(state);
    }

    self.transition_set.goto_map.hash(state);
  }
}

impl PartialEq for TransitionSet2 {
  fn eq(&self, other: &Self) -> bool {
    if self.transition_set.action_map.len() != other.transition_set.action_map.len() {
      return false;
    }

    self
      .transition_set
      .action_map
      .iter()
      .zip(other.transition_set.action_map.iter())
      .all(
        |((action1, terms1), (action2, terms2))| match (action1, action2) {
          (Action::Shift(lr_table_entry1), Action::Shift(lr_table_entry2)) => {
            lr_table_entry1 == lr_table_entry2
          }
          (Action::Reduce(prod_rule_ref1), Action::Reduce(prod_rule_ref2)) => {
            prod_rule_ref1.prod_ptr() == prod_rule_ref2.prod_ptr()
              && prod_rule_ref1
                .rules()
                .construction_pattern_eq(prod_rule_ref2.rules())
          }
          (Action::Terminate(prod_rule_ref1), Action::Terminate(prod_rule_ref2)) => {
            prod_rule_ref1.prod_ptr() == prod_rule_ref2.prod_ptr()
              && prod_rule_ref1
                .rules()
                .construction_pattern_eq(prod_rule_ref2.rules())
          }
          _ => false,
        } && terms1 == terms2,
      ) && self.transition_set.goto_map == other.transition_set.goto_map
  }
}

impl Eq for TransitionSet2 {}

struct StateMap {
  map: HashMap<Rc<LRTableEntry>, Rc<LRTableEntry>>,
}

impl StateMap {
  fn new() -> Self {
    Self {
      map: HashMap::new(),
    }
  }

  fn is_empty(&self) -> bool {
    self.map.is_empty()
  }

  fn insert(&mut self, from: Rc<LRTableEntry>, to: Rc<LRTableEntry>) {
    self.map.insert(from, to);
  }

  fn remap(&mut self, mut entry: Rc<LRTableEntry>) -> Rc<LRTableEntry> {
    while let Some(remap) = self.map.get(&entry) {
      let remap = remap.clone();
      if let Some(parent) = self.map.get(&remap) {
        self.map.insert(entry, parent.clone());
      }
      entry = remap;
    }
    entry
  }
}

impl Display for StateMap {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self
      .map
      .iter()
      .try_for_each(|(e1, e2)| write!(f, "{} -> {}", e1, e2))
  }
}

pub struct LRTable {
  pub states: HashSet<Rc<LRTableEntry>>,
  pub initial_state: Rc<LRTableEntry>,
}

impl LRTable {
  fn calculate_transitions(
    states: &mut HashSet<Rc<LRTableEntry>>,
    grammar: &Grammar,
    first_table: &mut ProductionFirstTable,
    lr_state_builder: &LRStateBuilder,
    parent_lr_state: Option<Rc<LRTableEntry>>,
    next_uid: &mut u64,
  ) -> ParseResult<Rc<LRTableEntry>> {
    let lr_table_entry = LRTableEntry::from(lr_state_builder.clone());
    if let Some(mut prior_lr_state) = states.take(&lr_table_entry) {
      if let Some(parent_state) = parent_lr_state {
        unsafe {
          Rc::get_mut_unchecked(&mut prior_lr_state)
            .lr_state_mut()
            .add_parent(parent_state);
        }
      }
      states.insert(prior_lr_state.clone());
      return Ok(prior_lr_state);
    }
    // eprintln!("line: {}", lr_state_builder);

    let lr_state = Rc::new(lr_table_entry);
    assert!(states.insert(lr_state.clone()));

    let closure = Closure::from_lr_states(lr_state_builder, first_table);
    // eprintln!("\tclozure: {}", closure);
    let transitions = closure.transitions(grammar)?;

    let mut transition_set = TransitionSet::new();

    for (term, action_builder) in transitions.action_map {
      match action_builder {
        ActionBuilder::Shift(lr_state_builder) => {
          let child_lr_state = Self::calculate_transitions(
            states,
            grammar,
            first_table,
            &lr_state_builder,
            Some(lr_state.clone()),
            next_uid,
          )?;
          transition_set.insert_action(term.clone(), Action::Shift(child_lr_state));
        }
        ActionBuilder::Reduce(prod_ref) => {
          transition_set.insert_action(term.clone(), Action::Reduce(prod_ref));
        }
        ActionBuilder::Terminate(prod_ref) => {
          transition_set.insert_action(term.clone(), Action::Terminate(prod_ref));
        }
      }
    }

    for (prod_ref, lr_state_builder) in transitions.goto_map {
      let child_lr_state = Self::calculate_transitions(
        states,
        grammar,
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

  /// Merge all states which have the same transition set iteratively, until
  /// no more merges can be done.
  fn merge_redundant_states(&mut self) {
    loop {
      let mut transition_set_map: HashMap<TransitionSet2, Rc<LRTableEntry>> = HashMap::new();
      let mut remapped_states = StateMap::new();

      self.states.iter().for_each(|lr_table_entry| {
        let transition_set: TransitionSet2 = lr_table_entry.lr_state().transitions.clone().into();
        // eprintln!("Processing {}", transition_set.transition_set);
        if let Some((transition_set, other_entry)) =
          transition_set_map.remove_entry(&transition_set)
        {
          // eprintln!("cloning");
          let mut new_entry = other_entry.as_ref().clone();
          new_entry
            .lr_state_mut()
            .merge(lr_table_entry.lr_state().clone());
          let new_entry = Rc::new(new_entry);
          // eprintln!(
          //   "MERGING ENTRIES: {} + {} = {}",
          //   other_entry, lr_table_entry, new_entry
          // );
          // eprintln!("inserting");
          transition_set_map.insert(transition_set, new_entry.clone());
          // eprintln!("done");

          // if let x = remapped_states.remap(other_entry.clone()) {
          //   // If other_entry already has a remap, then map to it's remapped state instead.
          // }
          remapped_states.insert(lr_table_entry.clone(), new_entry.clone());
          remapped_states.insert(other_entry, new_entry.clone());
        } else {
          // eprintln!("cloning/inserting");
          transition_set_map.insert(
            lr_table_entry.lr_state().transitions.clone().into(),
            lr_table_entry.clone(),
          );
          // eprintln!("done");
        }
      });

      // eprintln!("checking remapped states");
      if remapped_states.is_empty() {
        break;
      }

      // eprintln!("trans set map:");
      // transition_set_map.iter().for_each(|(trans_set, lr_entry)| {
      //   let mut hasher = std::collections::hash_map::DefaultHasher::new();
      //   trans_set.hash(&mut hasher);
      //   eprintln!("{} ({})", lr_entry, hasher.finish());
      // });
      // eprintln!("remapped states:");
      // eprintln!("{}", remapped_states);
      // eprintln!("Done");

      // Clear so the rc's in the map are unreferenced.
      transition_set_map.clear();

      // eprintln!("redoing new states");
      let new_states = self
        .states
        .clone()
        .into_iter()
        .map(|state| {
          // eprintln!("remapping");
          let mut state = remapped_states.remap(state);
          let state_ref = unsafe { Rc::get_mut_unchecked(&mut state) };
          // eprintln!("update refs");
          state_ref.lr_state_mut().update_refs(&mut remapped_states);
          state
        })
        .collect::<HashSet<_>>();
      // eprintln!("reindexing");
      self.states = new_states
        .into_iter()
        .enumerate()
        .map(|(idx, mut state)| {
          let state_ref = unsafe { Rc::get_mut_unchecked(&mut state) };
          state_ref.lr_state_mut().uid = idx as u64;
          state
        })
        .collect();
      // eprintln!("done");
      self.initial_state = remapped_states.remap(self.initial_state.clone());
    }
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

    eprintln!("Calculate transitions");
    let initial_state = Self::calculate_transitions(
      &mut states,
      grammar,
      &mut first_table,
      &initial_lr_state,
      None,
      &mut next_uid,
    )?;

    let mut lr_table = Self {
      states,
      initial_state,
    };
    eprintln!("merge redundant states ({})", lr_table.states.len());
    lr_table.merge_redundant_states();
    eprintln!("merged, now {}", lr_table.states.len());

    Ok(lr_table)
  }
}

impl Display for LRTable {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    let mut states = self.states.iter().collect::<Vec<_>>();
    states.sort_by(|s1, s2| s1.lr_state().uid.cmp(&s2.lr_state().uid));

    for state in states.iter() {
      write!(f, "state {}: {}\n", state.lr_state().uid, state)?;
    }
    Ok(())
  }
}
