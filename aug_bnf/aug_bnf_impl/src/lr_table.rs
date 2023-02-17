use proc_macro::Span;
use proc_macro_error::abort;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

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

// TODO
struct TransitionSet {}

enum FirstCacheState {
  Hit(HashSet<Terminal>),
  // The terminals for this state are currently being calculated.
  Pending,
}

/// A cache of the sets of possible first elements seen in a production rule,
/// given the production's name.
type ProductionFirstTable = HashMap<ProductionName, FirstCacheState>;

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

  pub fn calculate_first_set(&self, first_cache: &mut ProductionFirstTable) -> HashSet<Terminal> {
    if self.pos == 0 {
      if let Some(state) = first_cache.get(&self.name) {
        match &state {
          FirstCacheState::Hit(terms) => {
            return terms.clone();
          }
          FirstCacheState::Pending => {
            // If this production is in a pending state, that means some
            // recursive parent caller is calculating this state, so ignore more
            // instances of the same state.
            return HashSet::new();
          }
        };
      } else {
        // Set the cache state to pending.
        first_cache.insert(self.name.clone(), FirstCacheState::Pending);
      }
    }

    debug_assert!(self.rules.rules.len() > self.pos as usize);
    let mut terms = HashSet::new();

    match self.next_sym() {
      Some(ProductionRule::Intermediate(production_ref)) => {
        let production: &Production = &production_ref;
        // calculate_first_set doesn't ever use possible_lookaheads, so we can
        // set it to the empty set.
        let prod_state = Self::from_production(production, vec![]);
        terms.extend(
          prod_state
            .into_iter()
            .fold(HashSet::new(), |mut terms, state| {
              terms.extend(state.calculate_first_set(first_cache));
              terms
            }),
        );
      }
      Some(ProductionRule::Terminal(terminal)) => {
        if let Terminal::Epsilon(_) = terminal {
          terms.extend(self.advance().calculate_first_set(first_cache));
        } else {
          terms.insert(terminal.clone());
        }
      }
      // If the production is finished, return epsilon.
      None => {
        terms.insert(Terminal::Epsilon(Span::call_site()));
      }
    }

    if self.pos == 0 {
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

impl<'a> Hash for ProductionState<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
    self.pos.hash(state);
  }
}

impl<'a> PartialEq for ProductionState<'a> {
  // Production states are grouped into equivalence classes based only on their
  // name and position, not lookaheads, as those don't affect the `first` set of
  // the state.
  fn eq(&self, other: &Self) -> bool {
    self.name == other.name && self.pos == other.pos
  }
}

impl<'a> Eq for ProductionState<'a> {}

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

struct LRState<'a> {
  states: Vec<ProductionState<'a>>,
}

impl<'a> LRState<'a> {
  // Returns the list of possible first terminals that this production could
  // match after position `pos`.
  pub fn calculate_transitions(&self, pos: u32) -> Vec<(Terminal, ProductionState<'a>)> {
    unimplemented!();
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
