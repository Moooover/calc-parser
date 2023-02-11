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

impl<'a, T: Display> Display for AstNode<'a, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      AstNode::Terminal(t) => {
        write!(f, "{}", t)
      }
      AstNode::Intermediate((t, substr, node)) => {
        write!(f, "{} (", t)?;
        fmt2(substr, f)?;
        write!(f, ")")
      }
    }
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

  fn root_rule(&self) -> &Vec<Vec<T>> {
    if let Some(rule) = self.productions.get(&self.root) {
      return rule;
    }
    panic!("Root {} not found!", self.root);
  }

  pub fn add_production(&mut self, prod: Production<T>) {
    let rules = self.productions.entry(prod.from).or_insert(Vec::new());
    rules.push(prod.to);
  }

  fn parse_slice<'a, 'b>(
    &'a self,
    rules: &'a Vec<Vec<T>>,
    items: &'b [&'a T],
  ) -> Option<(Vec<AstNode<'a, T>>, &'b [&'a T])> {
    println!(
      "Checking {}",
      items
        .iter()
        .fold("".to_string(), |s, item| s + &format!("{}", item) + ", ")
    );
    'outer: for rule in rules.iter() {
      let mut children: Vec<AstNode<'a, T>> = Vec::new();
      let mut item_seq = items;
      println!(
        "rule {} ({})",
        rule
          .iter()
          .fold("".to_string(), |s, item| s + &format!("{}", item) + ", "),
        rules.len()
      );

      for sym in rule.iter() {
        if let Some(sym_rules) = self.productions.get(sym) {
          println!("Trying rule {}", sym);
          println!(
            "{}",
            sym_rules.iter().fold("".to_string(), |s, rule| {
              rule
                .iter()
                .fold(s + ", ", |s, item| s + &format!("{}", item) + ", ")
            })
          );
          // This is an intermediate node.
          if let Some((ast_nodes, new_items)) = self.parse_slice(sym_rules, items) {
            children.push(AstNode::Intermediate((
              sym,
              Vec::from(&items[..items.len() - new_items.len()]),
              ast_nodes,
            )));
            item_seq = new_items;
          } else {
            continue 'outer;
          }
        } else {
          println!("matching terminal {}", sym);
          if *sym == self.end_of_stream {
            if item_seq.len() == 0 {
              return Some((vec![AstNode::Terminal(&self.end_of_stream)], item_seq));
            } else {
              continue 'outer;
            }
          }
          // This is a terminal node.
          if item_seq.len() > 0 && rule[0] == *sym {
            children.push(AstNode::Terminal(sym));
            item_seq = &item_seq[1..];
          } else {
            continue 'outer;
          }
        }
      }

      return Some((children, item_seq));
    }

    return None;
  }

  pub fn parse<'a, I: Iterator<Item = &'a T>>(&'a self, iter: I) -> Option<Vec<AstNode<'a, T>>> {
    let items: Vec<&'a T> = iter.collect();
    if let Some((ast_node, _rem)) = self.parse_slice(self.root_rule(), &items[..]) {
      return Some(ast_node);
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
