use std::cmp::{Eq, PartialEq};
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;

fn fmt2<T: Display>(v: &Vec<T>, f: &mut std::fmt::Formatter) -> std::fmt::Result {
  for (i, c) in v.iter().enumerate() {
    if i > 0 {
      write!(f, " ")?;
    }
    write!(f, "{}", c)?;
  }
  Ok(())
}

pub struct Production<T: Display> {
  pub from: T,
  pub to: Vec<T>,
}

impl<T: Display> Production<T> {
  pub fn new(from: T, to: Vec<T>) -> Self {
    Self { from, to }
  }
}

impl<T: Display> Display for Production<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{} -> ", self.from)?;
    fmt2(&self.to, f)
  }
}

pub struct AstNode<'a, T: Display> {
  pub production: Production<T>,
  pub substr: &'a [&'a T],
}

impl<'a, T: Display> AstNode<'a, T> {
  pub fn new(production: Production<T>, substr: &'a [&'a T]) -> Self {
    Self {
      production,
      substr: substr,
    }
  }
}

impl<'a, T: Display> Display for AstNode<'a, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{} (", self.production)?;
    fmt2(&Vec::from(self.substr), f)?;
    write!(f, ")")
  }
}

pub struct GrammarParser<T: Display + Eq + PartialEq + Hash> {
  productions: HashMap<T, Vec<Vec<T>>>,
  root: T,
}

impl<T: std::fmt::Debug + Display + Eq + PartialEq + Hash> GrammarParser<T> {
  pub fn new(root: T) -> Self {
    Self {
      productions: HashMap::new(),
      root,
    }
  }

  fn root_rule(&self) -> &Vec<T> {
    if let Some(rule) = self.productions.get(&self.root) {
      if rule.len() != 1 {
        panic!("Root rule has more than 1 possibility!");
      }
      return &rule[0];
    }
    panic!("Root {} not found!", self.root);
  }

  pub fn add_production(&mut self, prod: Production<T>) {
    let rules = self.productions.entry(prod.from).or_insert(Vec::new());
    rules.push(prod.to);
  }

  fn parse_slice<'a>(&'a self, rule: &[T], items: &'a [&T]) -> Vec<&'a [&T]> {
    if rule.len() == 0 {
      return vec![items];
    }

    if let Some(rules) = self.productions.get(&rule[0]) {
      let mut return_vals = Vec::new();

      // This is an intermediate node.
      for irule in rules {
        for new_items in self.parse_slice(&irule[..], items) {
          return_vals.extend(self.parse_slice(&rule[1..], new_items));
        }
      }

      return return_vals;
    } else {
      // This is a terminal node.
      if items.len() > 0 && rule[0] == *items[0] {
        return self.parse_slice(&rule[1..], &items[1..]);
      } else {
        return Vec::new();
      }
    }
  }

  pub fn parse<'a, I: Iterator<Item = &'a T>>(&'a self, iter: I) -> bool {
    let items: Vec<&T> = iter.collect();
    return self
      .parse_slice(&self.root_rule()[..], &items[..])
      .iter()
      .any(|text| text.len() == 0);
  }
}

impl<T: Display + Eq + PartialEq + Hash> Display for GrammarParser<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    for (i, (from, to)) in self.productions.iter().enumerate() {
      write!(f, "{} -> ", from)?;
      fmt2(&to[0], f)?;

      for option in to.iter().skip(1) {
        write!(f, "\n     ")?;
        fmt2(&option, f)?;
      }

      if i < self.productions.len() - 1 {
        write!(f, "\n")?;
      }
    }
    Ok(())
  }
}
