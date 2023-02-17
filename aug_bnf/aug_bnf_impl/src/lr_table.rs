use proc_macro_error::abort;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::production::{
  Production, ProductionName, ProductionRef, ProductionRefT, ProductionRule, ProductionRules,
  Terminal, TerminalSym,
};

use crate::production::Grammar;

enum Action {
  Shift(Terminal),
  Reduce(ProductionRef),
}

struct Transition<'a> {
  action: Action,
  next_state: ProductionState<'a>,
}

struct TransitionSet {
  todo!();
}

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

  fn from_production(production: &'a Production, possible_lookaheads: Vec<Terminal>) -> Vec<Self> {
    production
      .rules
      .iter()
      .map(|rules| Self {
        name: &production.name,
        rules: &rules,
        pos: 0,
        possible_lookaheads: possible_lookaheads.clone(),
      })
      .collect()
  }

  pub fn is_complete(&self) -> bool {
    self.pos == self.rules.rules.len()
  }

  // Returns the next symbol in this production, if there are any symbols left.
  pub fn next_sym(&self) -> Option<&'a ProductionRule> {
    if self.is_complete() {
      return None;
    }

    return Some(&self.rules.rules[self.pos]);
  }

  pub fn advance(&self) -> ProductionState<'a> {
    debug_assert!(self.pos < self.rules.rules.len());
    Self {
      pos: self.pos + 1,
      ..self.clone()
    }
  }
}

struct LRState<'a> {
  states: Vec<ProductionState<'a>>,
}

impl<'a> LRState<'a> {
  // Returns the list of possible first terminals that this production could
  // match after position `pos`.
  pub fn calculate_transitions(&self, pos: u32) -> Vec<(Terminal, ProductionState<'a>)> {
    debug_assert!(self.rules.rules.len() > pos as usize);
    let mut terms = Vec::new();
    let mut pending_rules = VecDeque::new();
    let mut visited_rules = HashSet::new();

    pending_rules.push_back(self.clone());
    visited_rules.insert(self.name);

    while let Some(rule) = pending_rules.pop_front() {
      match rule.next_sym() {
        Some(ProductionRule::Intermediate(production_ref)) => {
          let production: &Production = &production_ref;
          // let next_production = production.advance();
          pending_rules.extend(Self::from_production(
            production,
            vec![],
            // next_production.first_after(0).map(|(term, _state)| term),
          ));
        }
        Some(ProductionRule::Terminal(terminal)) => {
          if let Terminal::Epsilon(_) = terminal {
            pending_rules.push_back(rule.advance());
          } else {
            terms.push((terminal.clone(), rule));
          }
        }
        None => panic!("Unexpected finished production"),
      }
    }

    return terms;
  }
}

/// A state in the parsing DFA, which contains the set of all possible
/// productions that we could currently be parsing. Note that these rules must
/// be compatible with each other, meaning they have all the same tokens before
/// the '.'.
struct Closure<'a> {
  states: Vec<ProductionState<'a>>,
}

impl<'a> From<LRState<'a>> for Closure<'a> {
  // List all derivative states from this one via application of production
  // rules to nonterminal symbols immediately following "pos".
  fn from(lr_state: LRState<'a>) -> Self {
    let mut queue: VecDeque<ProductionState<'a>> = VecDeque::new();
    let mut closure = Vec::new();

    queue.extend(lr_state.states);

    while let Some(state) = queue.pop_front() {
      if !state.is_complete() {
        match state.next_sym() {
          Some(ProductionRule::Intermediate(production)) => match &production.production {
            ProductionRefT::Resolved(prod_ptr) => {
              let prod = prod_ptr.upgrade().unwrap();
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
