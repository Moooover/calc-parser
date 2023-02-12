use proc_macro::Span;
use proc_macro_error::{abort, proc_macro_error};
use std::collections::HashMap;

use crate::symbol::{Operator, Symbol, SymbolT};

struct TerminalSym {
  name: String,
  span: Span,
}

struct ProductionName {
  name: String,
  alias: Option<String>,
  span: Span,
}

enum ProductionRule<'a> {
  Intermediate(&'a Production<'a>),
  Terminal(TerminalSym),
}

struct ProductionRules<'a> {
  rules: Vec<ProductionRule<'a>>,
  span: Span,
}

struct Production<'a> {
  name: ProductionName,
  rules: Vec<ProductionRules<'a>>,
  span: Span,
}

impl<'a> Production<'a> {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut T) -> Option<Self> {
    let sym = iter.next()?;

    let production_name = match &sym.sym {
      SymbolT::Ident(ident) => {
        ProductionName {
          name: ident.to_string(),
          // You can't alias the production definition.
          alias: None,
          span: sym.span,
        }
      }
      _ => {
        abort!(sym.span, "Expected production rule name.");
      }
    };

    let arrow = iter.next().unwrap_or_else(|| {
      abort!(
        production_name.span,
        "Expected \"=>\" to follow production name."
      )
    });
    match arrow.sym {
      SymbolT::Op(Operator::Arrow) => {}
      _ => {
        abort!(arrow.span, "Expected \"=>\" to follow production name.");
      }
    }

    return None;
  }
}

pub struct Grammar<'a> {
  productions: HashMap<&'a str, Production<'a>>,
  start_rule: &'a str,
}

impl<'a> Grammar<'a> {
  pub fn from(token_stream: Vec<Symbol>) -> Self {
    let productions: HashMap<&'a str, Production<'a>> = HashMap::new();
    let start_rule: Option<&'a str> = None;

    let mut token_iter = token_stream.into_iter();
    while let Some(production) = Production::parse(&mut token_iter) {}

    Self {
      productions,
      start_rule: start_rule.unwrap(),
    }
  }
}
