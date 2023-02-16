use proc_macro_error::abort;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::production::{
  Production, ProductionName, ProductionRef, ProductionRule, ProductionRules, Terminal, TerminalSym,
};

use crate::production::Grammar;

/// A production state is an instance of a production and how far through the
/// production we've parsed so far (represented by a dot).
///
/// i.e. A -> b . C d
/// indicates that b has already been parsed, and we're ready to parse C d.
#[derive(Clone)]
struct ProductionState<'a> {
  // The name of the production, i.e. the LHS of A -> b C d ...
  name: &'a ProductionName,
  // The rules that make up this production, i.e. the RHS.
  rules: &'a ProductionRules,
  // Ranges from [0, rules.len()], and is the position of the dot.
  pos: usize,
  // The list of possible tokens that can follow this rule.
  possible_lookaheads: Vec<Terminal>,
}

impl<'a> ProductionState<'a> {
  pub fn new(
    name: &'a ProductionName,
    rules: &'a ProductionRules,
    possible_lookaheads: Vec<Terminal>,
  ) -> Self {
    Self {
      name,
      rules,
      pos: 0,
      possible_lookaheads,
    }
  }

  // Given the list of production rules, returns the list of possible first
  // terminals that this production could match.
  fn production_first(rules: &ProductionRules) -> Vec<Terminal> {
    debug_assert!(rules.rules.len() > 0);
    let mut terms = Vec::new();
    let mut pending_rules = VecDeque::new();
    // let mut visited_rules = HashSet::new();

    pending_rules.push_back(rules);

    while let Some(rule) = pending_rules.pop_front() {
      match &rule.rules[0] {
        ProductionRule::Intermediate(production_ref) => {
          let production: &Production = &production_ref;
        }
        ProductionRule::Terminal(terminal) => {
          if let Terminal::Epsilon(_) = terminal {
            // Disallow productions containing epsilon that don't contain only
            // one epsilon.
            debug_assert!(rules.rules.len() == 1);
          }
          terms.push(terminal.clone());
        }
      }
    }

    return terms;
  }

  pub fn advance(&self) -> Vec<(Terminal, ProductionState<'a>)> {
    debug_assert!(self.pos < self.rules.rules.len());
    let mut result = Vec::new();

    match &self.rules.rules[self.pos] {
      ProductionRule::Intermediate(production_ref) => {}
      ProductionRule::Terminal(terminal) => {
        result.push((
          terminal.clone(),
          Self {
            pos: self.pos + 1,
            ..self.clone()
          },
        ));
      }
    };

    return result;
  }
}

/// A state in the parsing DFA, which contains the set of all possible
/// productions that we could currently be parsing. Note that these rules must
/// be compatible with each other, meaning they have all the same tokens before
/// the '.'.
struct Closure<'a> {
  states: Vec<ProductionState<'a>>,
  uid: u32,
}

impl<'a> Closure<'a> {
  // List all derivative states from this one via application of production
  // rules to nonterminal symbols immediately following "pos".
  pub fn closure_from(&self) -> Self {
    let mut queue: VecDeque<ProductionState<'a>> = VecDeque::new();
    let mut closure = Vec::new();

    queue.extend(self.states.clone());

    while let Some(state) = queue.pop_front() {
      closure.push(state);
    }

    return Self {
      states: closure,
      uid: 0,
    };
  }
}

enum Action {
  Shift(Terminal),
  Reduce(ProductionRef),
}

// LR table keys are pairs of (state_id, lookahead), which are used to look up
// the action that should be taken at this step.
type LRTableKey = (u32, String);

pub struct LRTable {
  entries: HashMap<LRTableKey, Action>,
}

impl From<Grammar> for LRTable {
  fn from(grammar: Grammar) -> Self {
    let mut table = LRTable {
      entries: HashMap::new(),
    };

    return table;
  }
}
