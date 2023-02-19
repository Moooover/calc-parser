use proc_macro::{Span, TokenStream, TokenTree};
use proc_macro_error::abort;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::Peekable;
use std::ops::Deref;
use std::rc::{Rc, Weak};

use crate::symbol::{Operator, Symbol, SymbolT};

#[derive(Debug)]
pub struct ParseError {
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

pub type ParseResult<T> = Result<T, ParseError>;

macro_rules! span_join {
  ($s1:expr) => {
    $s1
  };
  ($s1:expr $(,$s2:expr)+) => {
    $s1.join(span_join!($($s2),+)).unwrap()
  };
}

macro_rules! span_join_opt {
  ($s1:expr, $s2:expr) => {
    match $s1 {
      Some(__span) => __span.join($s2),
      None => Some($s2),
    }
  };
}

fn iter_span<I: Iterator<Item = Span>>(iter: I) -> Span {
  iter
    .fold(None, |agg_span: Option<Span>, span| {
      span_join_opt!(agg_span, span)
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

macro_rules! span_or_call_site {
  ($span:expr) => {
    match $span {
      Some(span) => span,
      None => Span::call_site(),
    }
  };
}

pub struct ParserState {
  next_production_uid: u32,
}

impl ParserState {
  pub fn new() -> Self {
    Self {
      next_production_uid: 0,
    }
  }

  pub fn next_prod_uid(&mut self) -> u32 {
    let uid = self.next_production_uid;
    self.next_production_uid += 1;
    return uid;
  }
}

#[derive(Clone, Debug)]
struct Type {
  pub tokens: TokenStream,
  pub span: Span,
}

impl Type {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let mut tokens = TokenStream::new();
    let mut span: Option<Span> = None;

    // Consume everything that isn't an '=>' symbol.
    loop {
      let sym = peek_symbol_or(iter, "Expected type.", Span::call_site())?;

      match sym.sym {
        SymbolT::Op(Operator::Arrow) => {
          break;
        }
        SymbolT::Op(Operator::Semicolon) => {
          break;
        }
        _ => {
          let sym = iter.next().unwrap();
          tokens.extend(sym.tokens);
          span = span_join_opt!(span, sym.span);
        }
      };
    }

    let span = span.unwrap();
    Ok(Type { tokens, span })
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "{}", self.tokens)
  }
}

#[derive(Clone, Debug)]
pub struct TerminalSym {
  pub tokens: TokenStream,
  pub span: Span,
}

// <TerminalSym> => <Ident>
#[derive(Clone, Debug)]
pub enum Terminal {
  // '$'
  EndOfStream(Span),
  // '!'
  Epsilon(Span),
  Sym(TerminalSym),
}

impl Terminal {
  pub fn span(&self) -> Span {
    match self {
      Terminal::EndOfStream(span) => *span,
      Terminal::Epsilon(span) => *span,
      Terminal::Sym(sym) => sym.span,
    }
  }

  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let mut tokens = TokenStream::new();
    let mut span: Option<Span> = None;

    loop {
      let sym = peek_symbol_or(
        iter,
        "Unexpected end of stream while parsing terminal symbol.",
        span_or_call_site!(span),
      )?;
      match &sym.sym {
        SymbolT::Ident(_) => {
          tokens.extend(sym.tokens.clone());
          span = span_join_opt!(span, sym.span);

          // Consume the symbol.
          iter.next();
        }
        SymbolT::Literal(_) => {
          tokens.extend(sym.tokens.clone());
          span = span_join_opt!(span, sym.span);

          // Consume the symbol.
          iter.next();
        }
        SymbolT::Op(Operator::Scope) => {
          tokens.extend(sym.tokens.clone());
          span = span_join_opt!(span, sym.span);

          // Consume the symbol.
          iter.next();
        }
        SymbolT::Op(Operator::DollarSign) => {
          // If we've already consumed some tokens, don't include this '$' in
          // the terminal.
          if tokens.is_empty() {
            let sym_span = sym.span;
            // Consume the symbol.
            iter.next();
            return Ok(Terminal::EndOfStream(sym_span));
          }
          break;
        }
        SymbolT::Op(Operator::Bang) => {
          // If we've already consumed some tokens, don't include this '!' in
          // the terminal.
          if tokens.is_empty() {
            let sym_span = sym.span;
            // Consume the symbol.
            iter.next();
            return Ok(Terminal::Epsilon(sym_span));
          }
          break;
        }
        _ => {
          break;
        }
      };
    }

    if tokens.is_empty() {
      let sym = peek_symbol_or(iter, "Expected terminal symbol.", span_or_call_site!(span))?;
      return ParseError::new("Unexpected token.", sym.span).into();
    }

    Ok(Terminal::Sym(TerminalSym {
      tokens,
      span: span.unwrap(),
    }))
  }
}

impl Hash for Terminal {
  fn hash<H: Hasher>(&self, state: &mut H) {
    match self {
      Terminal::EndOfStream(_) => {
        state.write_u64(0);
      }
      Terminal::Epsilon(_) => {
        state.write_u64(1);
      }
      Terminal::Sym(sym) => {
        state.write_u64(2);
        sym.tokens.clone().into_iter().for_each(|tt| match tt {
          TokenTree::Ident(ident) => {
            state.write_u64(3);
            ident.to_string().hash(state);
          }
          TokenTree::Punct(punct) => {
            state.write_u64(4);
            punct.as_char().hash(state);
          }
          _ => panic!("Unexpected token in terminal"),
        });
      }
    };
  }
}

impl PartialEq for Terminal {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Terminal::EndOfStream(_1), Terminal::EndOfStream(_2)) => true,
      (Terminal::Epsilon(_1), Terminal::Epsilon(_2)) => true,
      (Terminal::Sym(sym1), Terminal::Sym(sym2)) => std::iter::zip(
        sym1.tokens.clone().into_iter(),
        sym2.tokens.clone().into_iter(),
      )
      .all(|(token1, token2)| match (token1, token2) {
        (TokenTree::Ident(ident1), TokenTree::Ident(ident2)) => {
          ident1.to_string() == ident2.to_string()
        }
        (TokenTree::Punct(punct1), TokenTree::Punct(punct2)) => {
          punct1.as_char() == punct2.as_char()
        }
        _ => false,
      }),
      _ => false,
    }
  }
}

impl Eq for Terminal {}

impl Display for Terminal {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      Terminal::EndOfStream(_span) => write!(f, "$"),
      Terminal::Epsilon(_span) => write!(f, "!"),
      Terminal::Sym(sym) => write!(f, "{}", sym.tokens),
    }
  }
}

#[derive(Clone, Debug)]
pub struct ProductionName {
  name: String,
  // A unique ID for this production, determined by declaration order.
  uid: u32,
  type_spec: Option<Type>,
  span: Span,
}

impl ProductionName {
  pub fn parse<T: Iterator<Item = Symbol>>(
    iter: &mut Peekable<T>,
    state: &mut ParserState,
  ) -> ParseResult<Self> {
    let begin_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::BeginProd),
      "Expected production rule name, which must begin with a '<'.",
      Span::call_site()
    );

    let sym = next_symbol_or(iter, "Expected production name.", Span::call_site())?;

    let prod_name = match sym.sym {
      SymbolT::Ident(ident) => Ok(ident),
      _ => ParseError::new("Expected production name.", sym.span).into(),
    }?;

    let end_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::EndProd),
      "Expected '>' at the end of production rule name.",
      Span::call_site()
    );

    // Join all spans up to this point.
    let span = span_join!(begin_span, sym.span, end_span);

    let next_sym = peek_symbol_or(iter, "Expected => or : <type> after production name.", span)?;
    let type_spec = match next_sym.sym {
      SymbolT::Op(Operator::Colon) => {
        // Consume the colon.
        iter.next();

        Some(Type::parse(iter)?)
      }
      _ => None,
    };

    Ok(ProductionName {
      name: prod_name,
      type_spec,
      uid: state.next_prod_uid(),
      span,
    })
  }
}

impl Hash for ProductionName {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.uid.hash(state);
  }
}

impl PartialEq for ProductionName {
  fn eq(&self, other: &ProductionName) -> bool {
    return self.uid == other.uid;
  }
}

impl Eq for ProductionName {}

impl PartialOrd for ProductionName {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.uid.partial_cmp(&other.uid)
  }
}

impl Ord for ProductionName {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.uid.cmp(&other.uid)
  }
}

impl Display for ProductionName {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "<{}>", self.name)?;
    if let Some(type_spec) = &self.type_spec {
      write!(f, ": {}", type_spec)?;
    }
    Ok(())
  }
}

#[derive(Clone, Debug)]
pub enum ProductionRefT {
  Resolved(Weak<Production>),
  Unresolved(String),
}

impl Display for ProductionRefT {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      ProductionRefT::Resolved(production) => write!(f, "{}", production.upgrade().unwrap().name),
      ProductionRefT::Unresolved(name) => write!(f, "<{}?>", name),
    }
  }
}

// <ProductionRef> => "<" ( <Alias> ":" )? <Ident> ">"
#[derive(Clone, Debug)]
pub struct ProductionRef {
  pub production: ProductionRefT,
  pub alias: Option<String>,
  pub span: Span,
}

impl ProductionRef {
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

    let colon_or_end = next_symbol_or(
      iter,
      "Expected '>' at end of a production rule name.",
      sym.span,
    )?;

    match colon_or_end.sym {
      SymbolT::Op(Operator::EndProd) => Ok(Self {
        production: ProductionRefT::Unresolved(production_name),
        alias: None,
        span: span_join!(begin_span, sym.span, colon_or_end.span),
      }),
      SymbolT::Op(Operator::Colon) => {
        // This is an aliased rule.
        let alias = production_name;
        let alias_span = sym.span;

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
          "Expected '>' at the end of production rule name.",
          Span::call_site()
        );

        Ok(Self {
          production: ProductionRefT::Unresolved(production_name),
          alias: Some(alias),
          span: span_join!(
            begin_span,
            alias_span,
            colon_or_end.span,
            sym.span,
            end_span
          ),
        })
      }
      _ => ParseError::new("Expected '>' or ':'.", colon_or_end.span).into(),
    }
  }
}

impl Deref for ProductionRef {
  type Target = Production;

  fn deref(&self) -> &Self::Target {
    match &self.production {
      ProductionRefT::Resolved(resolved) => unimplemented!(), /*resolved.upgrade().unwrap()*/
      ProductionRefT::Unresolved(unresolved) => {
        panic!(
          "Attempt to resolve unresolved production ref {}",
          unresolved
        );
      }
    }
  }
}

impl Display for ProductionRef {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    if let Some(alias) = &self.alias {
      write!(f, "<{}: {}>", alias, self.production)
    } else {
      write!(f, "<{}>", self.production)
    }
  }
}

// <ProductionRule> => <ProductionRef> | <TerminalSym>
#[derive(Clone, Debug)]
pub enum ProductionRule {
  Intermediate(ProductionRef),
  Terminal(Terminal),
}

impl ProductionRule {
  pub fn span(&self) -> Span {
    match self {
      Self::Intermediate(intermediate) => intermediate.span,
      Self::Terminal(terminal) => terminal.span(),
    }
  }
}

impl ProductionRule {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

    match sym.sym {
      SymbolT::Op(Operator::BeginProd) => {
        Ok(ProductionRule::Intermediate(ProductionRef::parse(iter)?))
      }
      _ => Ok(ProductionRule::Terminal(Terminal::parse(iter)?)),
    }
  }
}

impl Display for ProductionRule {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      ProductionRule::Intermediate(intermediate) => {
        write!(f, "{}", intermediate)
      }
      ProductionRule::Terminal(term) => {
        write!(f, "{}", term)
      }
    }
  }
}

// <ProductionRules> => <ProductionRule> <ProductionRules>?
#[derive(Clone, Debug)]
pub struct ProductionRules {
  pub rules: Vec<ProductionRule>,
  pub span: Span,
}

impl ProductionRules {
  pub fn new(rules: Vec<ProductionRule>, span: Span) -> Self {
    Self { rules, span }
  }

  pub fn rule_at(&self, pos: u32) -> Option<&ProductionRule> {
    let pos = pos as usize;
    debug_assert!(pos <= self.rules.len());
    if pos >= self.rules.len() {
      return None;
    } else {
      return Some(&self.rules[pos]);
    }
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
          span = span_join_opt!(span, prod_rule.span());
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
pub struct Production {
  pub name: ProductionName,
  pub rules: Vec<ProductionRules>,
  pub span: Span,
}

impl Production {
  pub fn merge(&mut self, other: Production) {
    debug_assert!(self.name.name == other.name.name);
    self.rules.extend(other.rules);
  }

  pub fn rules(&self) -> &Vec<ProductionRules> {
    &self.rules
  }

  pub fn parse<T: Iterator<Item = Symbol>>(
    iter: &mut Peekable<T>,
    state: &mut ParserState,
  ) -> ParseResult<Self> {
    let production_name = ProductionName::parse(iter, state)?;

    let arrow_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::Arrow),
      "Expected \"=>\" to follow production name.",
      production_name.span
    );

    let production_rules = ProductionRules::parse(iter)?;
    let span = span_join!(
      production_name.span,
      arrow_span,
      iter_span(production_rules.iter().map(|rule| rule.span))
    );

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
        write!(f, "\n{}", " ".repeat(self.name.name.len() + 6))?;
      }
      write!(f, "{}", rule)?;
    }
    Ok(())
  }
}

enum ParsedLine {
  Production(Production),
  TerminalType(Type),
}

fn parse_line<T: Iterator<Item = Symbol>>(
  iter: &mut Peekable<T>,
  state: &mut ParserState,
) -> ParseResult<ParsedLine> {
  let sym = peek_symbol_or(iter, "Expected line.", Span::call_site())?;
  let sym_span = sym.span.clone();

  match &sym.sym {
    SymbolT::Ident(ident) => {
      if ident != "terminal" {
        return ParseError::new(
          "Expected either production rule or \"terminal\" symbol.",
          sym_span,
        )
        .into();
      }
      // Consume the "terminal" ident.
      iter.next();

      expect_symbol!(
        iter,
        SymbolT::Op(Operator::Colon),
        "Expected \":\" to follow \"terminal\" symbol.",
        sym_span
      );

      let type_spec = Type::parse(iter)?;

      expect_symbol!(
        iter,
        SymbolT::Op(Operator::Semicolon),
        "Expected \";\" to follow terminal type.",
        type_spec.span
      );

      Ok(ParsedLine::TerminalType(type_spec))
    }
    _ => Ok(ParsedLine::Production(Production::parse(iter, state)?)),
  }
}

#[derive(Debug)]
pub struct Grammar {
  productions: HashMap<String, Rc<Production>>,
  start_rule: String,
  terminal_type: Type,
}

impl Grammar {
  pub fn starting_rule(&self) -> Rc<Production> {
    self.productions.get(&self.start_rule).unwrap().clone()
  }

  pub fn from(token_stream: Vec<Symbol>) -> Self {
    let mut productions: HashMap<String, Rc<Production>> = HashMap::new();
    let mut parser_state = ParserState::new();
    let mut terminal_type = None;

    let mut token_iter = token_stream.into_iter().peekable();
    while let Some(_) = token_iter.peek() {
      match parse_line(&mut token_iter, &mut parser_state) {
        Ok(ParsedLine::Production(production)) => {
          match productions.get_mut(&production.name.name) {
            Some(prod) => {
              Rc::get_mut(prod).unwrap().merge(production);
            }
            None => {
              productions.insert(production.name.name.to_string(), Rc::new(production));
            }
          }
        }
        Ok(ParsedLine::TerminalType(type_spec)) => match terminal_type {
          Some(_) => {
            abort!(type_spec.span, "Cannot have more than one terminal type.");
          }
          None => {
            terminal_type = Some(type_spec);
          }
        },
        Err(err) => {
          err.raise();
        }
      }
    }

    if terminal_type.is_none() {
      abort!(
        Span::call_site(),
        "Must define the terminal type with a line \"terminal: <type>\""
      );
    }
    let terminal_type = terminal_type.unwrap();

    let mut grammar = Self {
      productions,
      start_rule: "".to_string(),
      terminal_type,
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
            ProductionRule::Intermediate(intermediate) => match &intermediate.production {
              ProductionRefT::Unresolved(name) => {
                if let Some(prod) = self.productions.get(name) {
                  ProductionRule::Intermediate(ProductionRef {
                    production: ProductionRefT::Resolved(Rc::downgrade(prod)),
                    alias: intermediate.alias.clone(),
                    span: intermediate.span,
                  })
                } else {
                  abort!(
                    intermediate.span,
                    format!("Unknown production rule {}", name)
                  );
                }
              }
              ProductionRefT::Resolved(_) => unreachable!(),
            },
            ProductionRule::Terminal(term) => ProductionRule::Terminal(term.clone()),
          };
          new_rule_list.push(rule);
        }

        new_rules_list.push(ProductionRules::new(new_rule_list, prod.span));
      }

      for prod in new_rules_list.iter() {
        for rule in prod.rules.iter() {
          match rule {
            ProductionRule::Intermediate(intermediate) => match &intermediate.production {
              ProductionRefT::Resolved(res) => {
                *all_keys
                  .get_mut(&Weak::upgrade(&res).unwrap().name.name)
                  .unwrap() += 1;
              }
              ProductionRefT::Unresolved(_) => unreachable!(),
            },
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
    write!(f, "terminal: {}\n", self.terminal_type)?;
    for (i, (_rule_name, rule)) in self.productions.iter().enumerate() {
      write!(f, "{}", rule)?;
      if i != self.productions.len() - 1 {
        write!(f, "\n")?;
      }
    }
    Ok(())
  }
}
