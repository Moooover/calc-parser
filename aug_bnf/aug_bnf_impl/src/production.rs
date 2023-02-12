use proc_macro::Span;
use proc_macro_error::abort;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::iter::Peekable;
use std::rc::{Rc, Weak};

use crate::symbol::{Operator, Symbol, SymbolT};

#[derive(Debug)]
struct ParseError {
  message: String,
  span: Span,
}

impl ParseError {
  pub fn new(message: &str, span: Span) -> Self {
    Self {
      message: String::from(message),
      span,
    }
  }

  pub fn raise(&self) -> ! {
    abort!(self.span, self.message);
  }
}

impl<T> From<ParseError> for ParseResult<T> {
  fn from(parse_err: ParseError) -> ParseResult<T> {
    Err(parse_err)
  }
}

type ParseResult<T> = Result<T, ParseError>;

fn iter_span<I: Iterator<Item = Span>>(iter: I) -> Span {
  iter
    .fold(None, |agg_span: Option<Span>, span| match agg_span {
      Some(agg_span) => agg_span.join(span),
      None => Some(span),
    })
    .unwrap()
}

fn peek_symbol_or<'a, I: Iterator<Item = Symbol>>(
  iter: &'a mut Peekable<I>,
  message: &str,
  span: Span,
) -> ParseResult<&'a Symbol> {
  if let Some(next) = iter.peek() {
    return Ok(next);
  } else {
    return ParseError::new(message, span).into();
  }
}

fn next_symbol_or<I: Iterator<Item = Symbol>>(
  iter: &mut I,
  message: &str,
  span: Span,
) -> ParseResult<Symbol> {
  if let Some(next) = iter.next() {
    return Ok(next);
  } else {
    return ParseError::new(message, span).into();
  }
}

macro_rules! expect_symbol {
  ($iter:expr, $expected:pat, $message:expr, $span:expr) => {{
    let sym = next_symbol_or($iter, $message, $span)?;
    match sym.sym {
      $expected => sym.span,
      _ => {
        return ParseError::new($message, sym.span).into();
      }
    }
  }};
}

#[derive(Clone, Debug)]
struct TerminalSym {
  pub name: String,
  pub span: Span,
}

// <TerminalSym> => <Ident>
#[derive(Clone, Debug)]
enum Terminal {
  EndOfStream(Span),
  Sym(TerminalSym),
}

impl Terminal {
  pub fn span(&self) -> Span {
    match self {
      Terminal::EndOfStream(span) => *span,
      Terminal::Sym(sym) => sym.span,
    }
  }

  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut T) -> ParseResult<Self> {
    let sym = next_symbol_or(iter, "Expected terminal symbol.", Span::call_site())?;

    match sym.sym {
      SymbolT::Ident(ident) => Ok(Terminal::Sym(TerminalSym {
        name: ident,
        span: sym.span,
      })),
      SymbolT::Literal(literal) => Ok(Terminal::Sym(TerminalSym {
        name: literal,
        span: sym.span,
      })),
      SymbolT::Op(Operator::DollarSign) => Ok(Terminal::EndOfStream(sym.span)),
      _ => ParseError::new("Expected terminal symbol.", sym.span).into(),
    }
  }
}

impl Display for Terminal {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      Terminal::EndOfStream(_span) => write!(f, "$"),
      Terminal::Sym(sym) => write!(f, "{}", sym.name),
    }
  }
}

// <ProductionName> => "<" <Ident> ">"
#[derive(Debug)]
struct ProductionName {
  pub name: String,
  pub alias: Option<String>,
  pub span: Span,
}

impl ProductionName {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut T) -> ParseResult<Self> {
    let begin_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::BeginProd),
      "Expected production rule name, which must begin with a '<'.",
      Span::call_site()
    );

    let sym = next_symbol_or(iter, "Dangling '<'", Span::call_site())?;

    let production_name = match &sym.sym {
      SymbolT::Ident(ident) => ident.to_string(),
      _ => {
        return ParseError::new("Expected production rule name.", sym.span).into();
      }
    };

    let end_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::EndProd),
      "Expected '>' at end of production rule name.",
      Span::call_site()
    );

    Ok(Self {
      name: production_name,
      // You can't alias the production definition.
      alias: None,
      span: begin_span.join(sym.span).unwrap().join(end_span).unwrap(),
    })
  }
}

impl Display for ProductionName {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "<{}>", self.name)
  }
}

// <ProductionRule> => <ProductionName> | <TerminalSym>
#[derive(Debug)]
enum ProductionRule {
  Intermediate(Weak<Production>),
  Terminal(Terminal),
  UnresolvedIntermediate(ProductionName),
}

impl ProductionRule {
  pub fn span(&self) -> Span {
    match self {
      Self::Intermediate(intermediate) => intermediate.upgrade().unwrap().span,
      Self::Terminal(terminal) => terminal.span(),
      Self::UnresolvedIntermediate(name) => name.span,
    }
  }
}

impl ProductionRule {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

    match sym.sym {
      SymbolT::Op(Operator::BeginProd) => Ok(ProductionRule::UnresolvedIntermediate(
        ProductionName::parse(iter)?,
      )),
      _ => Ok(ProductionRule::Terminal(Terminal::parse(iter)?)),
    }
  }
}

impl Display for ProductionRule {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      ProductionRule::Intermediate(intermediate) => {
        write!(f, "<{}>", intermediate.upgrade().unwrap().name)
      }
      ProductionRule::Terminal(term) => {
        write!(f, "{}", term)
      }
      ProductionRule::UnresolvedIntermediate(sym) => {
        write!(f, "<{}?>", sym)
      }
    }
  }
}

// <ProductionRules> => <ProductionRule> <ProductionRules>?
#[derive(Debug)]
struct ProductionRules {
  pub rules: Vec<ProductionRule>,
  pub span: Span,
}

impl ProductionRules {
  pub fn new(rules: Vec<ProductionRule>, span: Span) -> Self {
    Self { rules, span }
  }

  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Vec<Self>> {
    let mut rules = Vec::new();
    let mut span = None;

    loop {
      let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

      match sym.sym {
        SymbolT::Op(Operator::Semicolon) => {
          if rules.len() == 0 {
            return ParseError::new("Unexpected ';', expect production rule.", sym.span).into();
          } else {
            iter.next();
            return Ok(vec![Self {
              rules,
              span: span.unwrap(),
            }]);
          }
        }
        _ => {
          let prod_rule = ProductionRule::parse(iter)?;
          span = match span {
            Some(span) => span.join(prod_rule.span()),
            None => Some(prod_rule.span()),
          };
          rules.push(prod_rule);
        }
      }
    }
  }
}

impl Display for ProductionRules {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for rule in self.rules.iter() {
      write!(f, "{} ", rule)?;
    }
    Ok(())
  }
}

// <Production> => <ProductionName> "=>" <ProductionRules>
#[derive(Debug)]
struct Production {
  name: ProductionName,
  rules: Vec<ProductionRules>,
  span: Span,
}

impl Production {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let production_name = ProductionName::parse(iter)?;

    let arrow_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::Arrow),
      "Expected \"=>\" to follow production name.",
      production_name.span
    );

    let production_rules = ProductionRules::parse(iter)?;
    let span = production_name
      .span
      .join(arrow_span)
      .unwrap()
      .join(iter_span(production_rules.iter().map(|rule| rule.span)))
      .unwrap();

    Ok(Self {
      name: production_name,
      rules: production_rules,
      span,
    })
  }
}

impl Display for Production {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "{} => ", self.name)?;
    for (i, rule) in self.rules.iter().enumerate() {
      if i != 0 {
        write!(f, "\n{}", " ".repeat(self.name.name.len() + 4))?;
      }
      write!(f, "{}", rule)?;
    }
    Ok(())
  }
}

#[derive(Debug)]
pub struct Grammar {
  productions: HashMap<String, Rc<Production>>,
  start_rule: String,
}

impl Grammar {
  pub fn from(token_stream: Vec<Symbol>) -> Self {
    let mut productions: HashMap<String, Rc<Production>> = HashMap::new();

    let mut token_iter = token_stream.into_iter().peekable();
    while let Some(_) = token_iter.peek() {
      match Production::parse(&mut token_iter) {
        Ok(production) => {
          productions.insert(production.name.name.to_string(), Rc::new(production));
        }
        Err(err) => {
          err.raise();
        }
      }
    }

    let mut grammar = Self {
      productions,
      start_rule: "".to_string(),
    };

    grammar.resolve_refs();
    return grammar;
  }

  fn resolve_refs(&mut self) {
    let key_set: HashSet<_> = self.productions.keys().map(|k| k.to_string()).collect();
    let mut all_keys: HashMap<_, _> = self
      .productions
      .keys()
      .map(|k| (k.to_string(), 0u32))
      .collect();

    for key in key_set.iter() {
      let production = self.productions.get(key).unwrap();
      let mut new_rules_list = Vec::new();

      for prod in production.rules.iter() {
        let mut new_rule_list = Vec::new();

        for rule in prod.rules.iter() {
          let rule = match rule {
            ProductionRule::Intermediate(_intermedidate) => unreachable!(),
            ProductionRule::Terminal(term) => ProductionRule::Terminal(term.clone()),
            ProductionRule::UnresolvedIntermediate(name) => {
              if let Some(prod) = self.productions.get(&name.name) {
                ProductionRule::Intermediate(Rc::downgrade(prod))
              } else {
                abort!(name.span, format!("Unknown production rule {}", name));
              }
            }
          };
          new_rule_list.push(rule);
        }

        new_rules_list.push(ProductionRules::new(new_rule_list, prod.span));
      }

      for prod in new_rules_list.iter() {
        for rule in prod.rules.iter() {
          match rule {
            ProductionRule::Intermediate(intermediate) => {
              *all_keys
                .get_mut(&Weak::upgrade(&intermediate).unwrap().name.name)
                .unwrap() += 1;
            }
            _ => {}
          }
        }
      }
      unsafe {
        Rc::get_mut_unchecked(self.productions.get_mut(key).unwrap()).rules = new_rules_list;
      }
    }

    let unreffed_keys: Vec<_> = all_keys.iter().filter(|(_key, &cnt)| cnt == 0).collect();
    if unreffed_keys.len() == 0 {
      abort!(
        Span::call_site(),
        "No start production found, all productions are referenced."
      );
    }
    if unreffed_keys.len() > 1 {
      abort!(
        Span::call_site(),
        format!(
          "Production rules {} have no references. Expected only 1, which is the start rule.",
          unreffed_keys.iter().fold("".to_string(), |s, (key, _cnt)| {
            if s == "" {
              format!("<{}>", key)
            } else {
              format!("{}, <{}>", s, key)
            }
          })
        )
      )
    }

    self.start_rule = unreffed_keys[0].0.to_string();
  }
}

impl Display for Grammar {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    for (i, (_rule_name, rule)) in self.productions.iter().enumerate() {
      write!(f, "{}", rule)?;
      if i != self.productions.len() - 1 {
        write!(f, "\n")?;
      }
    }
    Ok(())
  }
}
