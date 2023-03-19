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

pub enum AstNode<'a, T: Display> {
  Terminal(&'a T),
  Intermediate((&'a T, Vec<&'a T>, Vec<AstNode<'a, T>>)),
}

impl<'a, T: Display> AstNode<'a, T> {
  fn write_to(&self, f: &mut std::fmt::Formatter, depth: usize) -> std::fmt::Result {
    match self {
      AstNode::Terminal(t) => {
        write!(f, "{}{} ", "  ".repeat(depth), t)
      }
      AstNode::Intermediate((t, substr, node)) => {
        write!(f, "{}{} (", "  ".repeat(depth), t)?;
        fmt2(substr, f)?;
        write!(f, ")")?;

        node.iter().try_for_each(|node| {
          write!(f, "\n")?;
          node.write_to(f, depth + 1)
        })
      }
    }
  }
}

impl<'a, T: Display> Clone for AstNode<'a, T> {
  fn clone(&self) -> Self {
    match self {
      AstNode::Terminal(term) => AstNode::Terminal(term),
      AstNode::Intermediate((sym, v1, v2)) => AstNode::Intermediate((sym, v1.clone(), v2.clone())),
    }
  }
}

impl<'a, T: Display> Display for AstNode<'a, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    self.write_to(f, 0)
  }
}

pub struct GrammarParser<T: Display + Eq + PartialEq + Hash> {
  productions: HashMap<T, Vec<Vec<T>>>,
  root: T,
  end_of_stream: T,
}

impl<T: std::fmt::Debug + Display + Eq + PartialEq + Hash> GrammarParser<T> {
  pub fn new(root: T, end_of_stream: T) -> Self {
    Self {
      productions: HashMap::new(),
      root,
      end_of_stream,
    }
  }

  fn root_rule(&self) -> &[T] {
    if let Some(rule) = self.productions.get(&self.root) {
      if rule.len() != 1 {
        panic!("Root rule has length != 1 ({})", rule.len());
      }
      return &rule[0][..];
    }
    panic!("Root {} not found!", self.root);
  }

  pub fn add_production(&mut self, prod: Production<T>) {
    let rules = self.productions.entry(prod.from).or_insert(Vec::new());
    rules.push(prod.to);
  }

  fn parse_slice<'a, 'b>(
    &'a self,
    rule_name: &'a T,
    rule: &'a [T],
    items: &'b [&'a T],
  ) -> Vec<(AstNode<'a, T>, &'b [&'a T])> {
    if rule.len() == 0 {
      return vec![(
        AstNode::Intermediate((rule_name, Vec::new(), Vec::new())),
        items,
      )];
    }

    println!(
      "rule {}",
      rule
        .iter()
        .fold("".to_string(), |s, item| s + &format!("{}", item) + ", ")
    );

    let sym = &rule[0];
    if let Some(sym_rules) = self.productions.get(sym) {
      // This is an intermediate node.
      let mut return_vals = Vec::new();

      for irule in sym_rules {
        let possibilities = self.parse_slice(sym, &irule[..], items);
        for (node, rem_items) in possibilities {
          return_vals.extend(
            self
              .parse_slice(rule_name, &rule[1..], rem_items)
              .into_iter()
              .map(|(s_node, rem_items)| {
                let new_node = match (node.clone(), s_node) {
                  (AstNode::Intermediate(a), AstNode::Intermediate(mut child_a)) => {
                    a.1.iter().rev().for_each(|c| {
                      child_a.1.insert(0, c);
                    });
                    child_a.2.insert(0, AstNode::Intermediate(a));
                    AstNode::Intermediate(child_a)
                  }
                  (_, _) => unreachable!(),
                };
                (new_node, rem_items)
              }),
          )
        }
      }

      return return_vals;
    } else {
      // This is a terminal node.
      println!("matching terminal {}", sym);

      if *sym == self.end_of_stream {
        if items.len() == 0 {
          return vec![(
            AstNode::Intermediate((
              rule_name,
              Vec::from(items),
              vec![AstNode::Terminal(&self.end_of_stream)],
            )),
            items,
          )];
        }
      } else if items.len() > 0 && *sym == *items[0] {
        let node = AstNode::Terminal(sym);

        return self
          .parse_slice(rule_name, &rule[1..], &items[1..])
          .into_iter()
          .map(|(s_node, rem_items)| {
            let new_node = match (node.clone(), s_node) {
              (AstNode::Terminal(node), AstNode::Intermediate(mut child_a)) => {
                child_a.1.insert(0, node);
                child_a.2.insert(0, AstNode::Terminal(node));
                AstNode::Intermediate((rule_name, child_a.1, child_a.2))
              }
              (_, _) => unreachable!(),
            };
            (new_node, rem_items)
          })
          .collect();
      }
    }

    return Vec::new();
  }

  pub fn parse<'a, I: Iterator<Item = &'a T>>(&'a self, iter: I) -> Option<AstNode<'a, T>> {
    let items: Vec<&'a T> = iter.collect();
    let mut possibilities = self.parse_slice(&self.root, self.root_rule(), &items[..]);
    if possibilities.len() > 0 {
      let (node, _rem) = possibilities.remove(0);
      return Some(node);
    } else {
      return None;
    }
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
