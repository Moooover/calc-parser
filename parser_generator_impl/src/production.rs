use proc_macro::{Span, TokenStream, TokenTree};
use proc_macro_error::abort;
use quote::quote;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::Peekable;
use std::rc::{Rc, Weak};

use crate::symbol::{Operator, Symbol, SymbolT};
use crate::util::{ParseError, ParseResult};

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
pub struct Type {
  pub tokens: TokenStream,
  pub span: Span,
}

impl Type {
  pub fn unit() -> Type {
    Type {
      tokens: quote::quote! { () }.into(),
      span: Span::call_site(),
    }
  }

  pub fn as_type(&self) -> syn::Type {
    syn::Type::Verbatim(self.tokens.clone().into())
  }

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
pub struct ParserName {
  pub name: String,
  pub span: Span,
}

impl ParserName {
  pub fn as_ident(&self) -> syn::Ident {
    syn::Ident::new(&self.name, self.span.into())
  }

  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let sym = next_symbol_or(iter, "Expected name.", Span::call_site())?;

    let name = match sym.sym {
      SymbolT::Ident(ident) => ident,
      _ => {
        return ParseError::new("Unexpected symbol.", sym.span).into();
      }
    };

    Ok(ParserName {
      name,
      span: sym.span,
    })
  }
}

impl Display for ParserName {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "{}", self.name)
  }
}

#[derive(Clone, Debug)]
pub struct TransparentSpan {
  span: Span,
}

impl TransparentSpan {
  pub fn span(&self) -> Span {
    self.span
  }
}

impl From<Span> for TransparentSpan {
  fn from(span: Span) -> Self {
    Self { span }
  }
}
impl Hash for TransparentSpan {
  fn hash<H: Hasher>(&self, _state: &mut H) {}
}

impl PartialEq for TransparentSpan {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl Eq for TransparentSpan {}

impl PartialOrd for TransparentSpan {
  fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
    Some(std::cmp::Ordering::Equal)
  }
}

impl Ord for TransparentSpan {
  fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
    std::cmp::Ordering::Equal
  }
}

#[derive(Clone, Debug)]
pub struct TerminalSym {
  pub tokens: TokenStream,
  pub span: TransparentSpan,
}

impl Hash for TerminalSym {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.tokens.clone().into_iter().for_each(|tt| match tt {
      TokenTree::Ident(ident) => {
        state.write_u64(3);
        ident.to_string().hash(state);
      }
      TokenTree::Literal(literal) => {
        state.write_u64(4);
        literal.to_string().hash(state);
      }
      TokenTree::Punct(punct) => {
        state.write_u64(5);
        punct.as_char().hash(state);
      }
      _ => abort!(self.span.span(), "Unexpected token in terminal"),
    });
  }
}

impl PartialEq for TerminalSym {
  fn eq(&self, other: &Self) -> bool {
    std::iter::zip(
      self.tokens.clone().into_iter(),
      other.tokens.clone().into_iter(),
    )
    .all(|(token1, token2)| match (token1, token2) {
      (TokenTree::Ident(ident1), TokenTree::Ident(ident2)) => {
        ident1.to_string() == ident2.to_string()
      }
      (TokenTree::Literal(literal1), TokenTree::Literal(literal2)) => {
        literal1.to_string() == literal2.to_string()
      }
      (TokenTree::Punct(punct1), TokenTree::Punct(punct2)) => punct1.as_char() == punct2.as_char(),
      _ => false,
    })
  }
}

impl Eq for TerminalSym {}

impl PartialOrd for TerminalSym {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self
      .tokens
      .to_string()
      .partial_cmp(&other.tokens.to_string())
  }
}

impl Ord for TerminalSym {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.tokens.to_string().cmp(&other.tokens.to_string())
  }
}

impl Display for TerminalSym {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "{}", self.tokens)
  }
}

// <TerminalSym> => <Ident>
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Terminal {
  // '$'
  EndOfStream(TransparentSpan),
  // '!'
  Epsilon(TransparentSpan),
  Sym(TerminalSym),
}

impl Terminal {
  pub fn span(&self) -> Span {
    match self {
      Terminal::EndOfStream(span) => span.span().clone(),
      Terminal::Epsilon(span) => span.span().clone(),
      Terminal::Sym(sym) => sym.span.span().clone(),
    }
  }

  /// Will expand to `Some(tokens)` if this is a `Terminal::Sym` or `_` if this
  /// is a `Terminal::EndOfStream`. `Terminal::Epsilon` should never call this.
  pub fn as_peek_pattern(&self) -> proc_macro2::TokenStream {
    match self {
      // Match anything for end of stream, including the actual end of stream
      // (None) or any token (Some(_)). This is to allow parsing of only part
      // of the input stream.
      Terminal::EndOfStream(span) => quote::quote_spanned!(span.span().into()=> _),
      Terminal::Epsilon(_) => unreachable!(),
      Terminal::Sym(sym) => {
        let tokens: proc_macro2::TokenStream = sym.tokens.clone().into();
        quote::quote! {
          Some(#tokens)
        }
      }
    }
  }

  pub fn is_end_of_stream(&self) -> bool {
    match self {
      Terminal::EndOfStream(_) => true,
      _ => false,
    }
  }

  pub fn as_sym_tokens(&self) -> proc_macro2::TokenStream {
    match self {
      Terminal::Sym(sym) => {
        let tokens: proc_macro2::TokenStream = sym.tokens.clone().into();
        quote::quote! {
          #tokens
        }
      }
      _ => unreachable!(),
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
          // Literals only appear alone.
          if !tokens.is_empty() {
            abort!(sym.span, "Unexpected literal.");
          }

          tokens.extend(sym.tokens.clone());
          span = span_join_opt!(span, sym.span);

          // Consume the symbol.
          iter.next();

          // Literals only appear alone.
          break;
        }
        SymbolT::Op(Operator::Scope) => {
          tokens.extend(sym.tokens.clone());
          span = span_join_opt!(span, sym.span);

          // Consume the symbol.
          iter.next();
        }
        SymbolT::Op(Operator::NumberSign) => {
          // If we've already consumed some tokens, don't include this '$' in
          // the terminal.
          if tokens.is_empty() {
            let sym_span = sym.span;
            // Consume the symbol.
            iter.next();
            return Ok(Terminal::EndOfStream(sym_span.into()));
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
            return Ok(Terminal::Epsilon(sym_span.into()));
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
      span: span.unwrap().into(),
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
        sym.hash(state);
      }
    };
  }
}

impl Display for Terminal {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match self {
      Terminal::EndOfStream(_span) => write!(f, "$"),
      Terminal::Epsilon(_span) => write!(f, "!"),
      Terminal::Sym(sym) => write!(f, "{}", sym),
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
  pub fn name(&self) -> &str {
    &self.name
  }

  pub fn span(&self) -> Span {
    self.span
  }

  pub fn has_type_spec(&self) -> bool {
    self.type_spec.is_some()
  }

  pub fn type_spec_as_type(&self) -> syn::Type {
    self.type_spec.clone().unwrap_or(Type::unit()).as_type()
  }

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
    write!(f, "{}", self.name)?;
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
  span: Span,
}

impl ProductionRef {
  // Creates a production ref from a production.
  pub fn new(prod_ptr: Weak<Production>) -> Self {
    Self {
      production: ProductionRefT::Resolved(prod_ptr.clone()),
      alias: None,
      span: prod_ptr.upgrade().unwrap().span,
    }
  }

  pub fn span(&self) -> Span {
    self.span
  }

  pub fn name(&self) -> String {
    match &self.production {
      ProductionRefT::Resolved(prod_ptr) => prod_ptr.upgrade().unwrap().name.name().to_string(),
      ProductionRefT::Unresolved(name) => name.to_string(),
    }
  }

  pub fn deref(&self) -> Rc<Production> {
    match &self.production {
      ProductionRefT::Resolved(resolved) => resolved.upgrade().unwrap().clone(),
      ProductionRefT::Unresolved(unresolved) => {
        panic!(
          "Attempt to resolve unresolved production ref {}",
          unresolved
        );
      }
    }
  }

  /// Makes a new reference to a particular rule of a production.
  pub fn rule_ref(&self, rule_idx: u32) -> ProductionRuleRef {
    debug_assert!((rule_idx as usize) < self.deref().rules().len());
    ProductionRuleRef::new(
      self.clone(),
      rule_idx,
      self.deref().rules().get(rule_idx as usize).unwrap().span(),
    )
  }

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

impl Hash for ProductionRef {
  fn hash<H: Hasher>(&self, state: &mut H) {
    match &self.production {
      ProductionRefT::Resolved(prod) => {
        state.write_u64(0);
        prod.upgrade().unwrap().hash(state);
      }
      ProductionRefT::Unresolved(name) => {
        state.write_u64(1);
        name.hash(state);
      }
    }
  }
}

impl PartialEq for ProductionRef {
  fn eq(&self, other: &Self) -> bool {
    match (&self.production, &other.production) {
      (ProductionRefT::Resolved(prod1), ProductionRefT::Resolved(prod2)) => {
        prod1.upgrade().unwrap() == prod2.upgrade().unwrap()
      }
      (ProductionRefT::Unresolved(name1), ProductionRefT::Unresolved(name2)) => name1 == name2,
      _ => false,
    }
  }
}

impl Eq for ProductionRef {}

impl PartialOrd for ProductionRef {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    match (&self.production, &other.production) {
      (ProductionRefT::Resolved(prod_ptr1), ProductionRefT::Resolved(prod_ptr2)) => prod_ptr1
        .upgrade()
        .unwrap()
        .name
        .partial_cmp(&prod_ptr2.upgrade().unwrap().name),
      (ProductionRefT::Resolved(_prod_ptr1), ProductionRefT::Unresolved(_prod_name2)) => {
        Some(std::cmp::Ordering::Greater)
      }
      (ProductionRefT::Unresolved(_prod_name1), ProductionRefT::Resolved(_prod_ptr2)) => {
        Some(std::cmp::Ordering::Less)
      }
      (ProductionRefT::Unresolved(prod_name1), ProductionRefT::Unresolved(prod_name2)) => {
        prod_name1.partial_cmp(&prod_name2)
      }
    }
  }
}

impl Ord for ProductionRef {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    match (&self.production, &other.production) {
      (ProductionRefT::Resolved(prod_ptr1), ProductionRefT::Resolved(prod_ptr2)) => prod_ptr1
        .upgrade()
        .unwrap()
        .name
        .cmp(&prod_ptr2.upgrade().unwrap().name),
      (ProductionRefT::Resolved(_prod_ptr1), ProductionRefT::Unresolved(_prod_name2)) => {
        std::cmp::Ordering::Greater
      }
      (ProductionRefT::Unresolved(_prod_name1), ProductionRefT::Resolved(_prod_ptr2)) => {
        std::cmp::Ordering::Less
      }
      (ProductionRefT::Unresolved(prod_name1), ProductionRefT::Unresolved(prod_name2)) => {
        prod_name1.cmp(&prod_name2)
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

  fn is_epsilon(&self) -> bool {
    if let ProductionRule::Terminal(term) = self {
      if let Terminal::Epsilon(_) = term {
        return true;
      }
    }
    return false;
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

// <Constructor> => proc_macro::Group
#[derive(Clone, Debug)]
pub struct Constructor {
  pub group: proc_macro::Group,
  span: TransparentSpan,
}

impl Constructor {
  pub fn new(group: proc_macro::Group, span: Span) -> Self {
    Self {
      group,
      span: span.into(),
    }
  }

  pub fn span(&self) -> Span {
    self.span.span()
  }
}

impl std::default::Default for Constructor {
  /// The default constructor is one that simply returns the unit type ("()").
  fn default() -> Self {
    Self {
      group: proc_macro::Group::new(proc_macro::Delimiter::Brace, quote! { () }.into()),
      span: proc_macro::Span::call_site().into(),
    }
  }
}

impl PartialEq for Constructor {
  // There is no meaningful way to compare constructors.
  fn eq(&self, _other: &Self) -> bool {
    false
  }
}

impl Eq for Constructor {}

impl Hash for Constructor {
  // Hash for constructor is a no-op.
  fn hash<H: Hasher>(&self, _state: &mut H) {}
}

impl Display for Constructor {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "{}", self.group)
  }
}

// <ProductionRules> => <ProductionRule> <ProductionRules>? <Constructor>
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProductionRules {
  pub rules: Vec<ProductionRule>,
  pub constructor: Option<Constructor>,
  span: TransparentSpan,
}

impl ProductionRules {
  fn new(rules: Vec<ProductionRule>, constructor: Option<Constructor>, span: Span) -> Self {
    Self {
      rules,
      constructor,
      span: span.into(),
    }
  }

  pub fn len(&self) -> u32 {
    self.rules.len() as u32
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

  pub fn span(&self) -> Span {
    self.span.span()
  }

  /// Hash function considering only the types of elements in the rules list,
  /// not particular values (i.e. terminals are considered equal, production
  /// rule refs are equal if they are refs to the same production rule).
  pub fn construction_pattern_hash<H: Hasher>(&self, state: &mut H) {
    for rule in &self.rules {
      match rule {
        ProductionRule::Intermediate(prod_rule_ref) => {
          state.write_u64(0);
          prod_rule_ref.hash(state);
        }
        ProductionRule::Terminal(_term) => {
          // All terminals are considered equal, since they're referenced the
          // same way in constructors.
          state.write_u64(1);
        }
      }
    }
    self.constructor.hash(state);
  }

  /// Equality comparison function considering only the types of elements in the
  /// rules list, not particular values (i.e. terminals are considered equal,
  /// production rule refs are equal if they are refs to the same production
  /// rule).
  pub fn construction_pattern_eq(&self, other: &ProductionRules) -> bool {
    if self.rules.len() != other.rules.len() {
      return false;
    }

    if !self
      .rules
      .iter()
      .zip(other.rules.iter())
      .all(|(rule1, rule2)| {
        match (rule1, rule2) {
          (
            ProductionRule::Intermediate(prod_rule_ref1),
            ProductionRule::Intermediate(prod_rule_ref2),
          ) => prod_rule_ref1 == prod_rule_ref2,
          (ProductionRule::Terminal(_term1), ProductionRule::Terminal(_term2)) => {
            // All terminals are considered equal, since they're referenced the
            // same way in constructors.
            true
          }
          _ => false,
        }
      })
    {
      return false;
    }

    return self.constructor == other.constructor;
  }

  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let mut rules = Vec::<ProductionRule>::new();
    let mut span: Option<Span> = None;
    let mut constructor: Option<Constructor> = None;

    loop {
      let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

      match &sym.sym {
        SymbolT::Op(Operator::Semicolon) | SymbolT::Op(Operator::Pipe) => {
          if rules.len() == 0 {
            return ParseError::new(
              &format!("Unexpected {}, expect production rule.", sym),
              sym.span,
            )
            .into();
          }
          break;
        }
        SymbolT::Group(group) => {
          constructor = Some(Constructor::new(
            group.clone(),
            iter_span(group.stream().clone().into_iter().map(|token| token.span())),
          ));

          // consume the symbol
          iter.next();
        }
        _ => {
          if constructor.is_some() {
            return ParseError::new(
              "Cannot have symbols following a production constructor.",
              sym.span,
            )
            .into();
          }
          let prod_rule = ProductionRule::parse(iter)?;
          span = span_join_opt!(span, prod_rule.span());
          rules.push(prod_rule);
        }
      }
    }

    if rules.len() != 1 {
      if let Some(epsilon) = rules
        .iter()
        .find(|sym| **sym == ProductionRule::Terminal(Terminal::Epsilon(Span::call_site().into())))
      {
        return ParseError::new(
          "Epsilon may only appear by itself, remove this epsilon.",
          epsilon.span(),
        )
        .into();
      }
    }

    return Ok(Self {
      rules: rules
        .into_iter()
        .filter(|rule| !rule.is_epsilon())
        .collect(),
      constructor,
      span: span.unwrap().into(),
    });
  }
}

impl Display for ProductionRules {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    if self.rules.len() == 0 {
      write!(f, "!")?;
    } else {
      for rule in self.rules.iter() {
        write!(f, "{} ", rule)?;
      }
    }
    Ok(())
  }
}

/// ProductionRuleRef is a reference to a particular instance of a rule.
///
/// Since these are only used in external code, and are not a part of the
/// grammar graph, we also take a strong reference to the Production.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProductionRuleRef {
  prod_ref: ProductionRef,
  prod_ptr: Rc<Production>,
  rule_idx: u32,
  span: TransparentSpan,
}

impl ProductionRuleRef {
  fn new(prod_ref: ProductionRef, rule_idx: u32, span: Span) -> Self {
    Self {
      prod_ptr: prod_ref.deref(),
      prod_ref,
      rule_idx,
      span: span.into(),
    }
  }

  pub fn name(&self) -> &str {
    self.prod_ptr.name()
  }

  pub fn span(&self) -> Span {
    self.span.span
  }

  pub fn prod_ref(&self) -> &ProductionRef {
    &self.prod_ref
  }

  pub fn prod_ptr(&self) -> &Rc<Production> {
    &self.prod_ptr
  }

  pub fn rules(&self) -> &ProductionRules {
    self.prod_ptr.rules().get(self.rule_idx as usize).unwrap()
  }
}

impl Display for ProductionRuleRef {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    write!(f, "<{}> => {}", self.name(), self.rules())
  }
}

// <Production> => <ProductionName> "=>" <ProductionRules>
//               | <Production> "|" <ProductionName> "=>" <ProductionRules>
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

  pub fn name(&self) -> &str {
    self.name.name()
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

    let mut production_rules_list = vec![ProductionRules::parse(iter)?];
    loop {
      let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

      match sym.sym {
        SymbolT::Op(Operator::Semicolon) => {
          break;
        }
        SymbolT::Op(Operator::Pipe) => {
          // Consume the pipe.
          iter.next();

          let production_rules = ProductionRules::parse(iter)?;
          production_rules_list.push(production_rules);
        }
        _ => {
          return ParseError::new(
            &format!("Unexpected {}, expect production rule.", sym),
            sym.span,
          )
          .into();
        }
      }
    }

    let semicolon_span = expect_symbol!(
      iter,
      SymbolT::Op(Operator::Semicolon),
      "Expected \";\" to end production definition.",
      production_name.span
    );

    let span = span_join!(
      production_name.span,
      arrow_span,
      iter_span(production_rules_list.iter().map(|rules| rules.span())),
      semicolon_span
    );

    Ok(Self {
      name: production_name,
      rules: production_rules_list,
      span,
    })
  }
}

impl Hash for Production {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
  }
}

impl PartialEq for Production {
  fn eq(&self, other: &Self) -> bool {
    self.name == other.name
  }
}

impl Eq for Production {}

impl PartialOrd for Production {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.name.partial_cmp(&other.name)
  }
}

impl Ord for Production {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.name.cmp(&other.name)
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

enum ParsedLine {
  Production(Production),
  Name(ParserName),
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
      if ident == "terminal" {
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
      } else if ident == "name" {
        // Consume the "name" ident.
        iter.next();

        expect_symbol!(
          iter,
          SymbolT::Op(Operator::Colon),
          "Expected \":\" to follow \"name\" symbol.",
          sym_span
        );

        let name = ParserName::parse(iter)?;

        expect_symbol!(
          iter,
          SymbolT::Op(Operator::Semicolon),
          "Expected \";\" to follow parser name.",
          name.span
        );

        Ok(ParsedLine::Name(name))
      } else {
        return ParseError::new(
          "Expected either production rule, \"name\", or \"terminal\" symbol.",
          sym_span,
        )
        .into();
      }
    }
    _ => Ok(ParsedLine::Production(Production::parse(iter, state)?)),
  }
}

#[derive(Debug)]
pub struct Grammar {
  productions: HashMap<String, Rc<Production>>,
  start_rule: String,
  pub parser_name: ParserName,
  pub terminal_type: Type,
}

impl Grammar {
  pub fn starting_rule(&self) -> ProductionRef {
    ProductionRef::new(Rc::downgrade(
      self.productions.get(&self.start_rule).unwrap(),
    ))
  }

  pub fn is_starting_rule(&self, prod_ref: &ProductionRef) -> bool {
    prod_ref.deref().name() == self.start_rule
  }

  pub fn from(token_stream: Vec<Symbol>) -> Self {
    let mut productions: HashMap<String, Rc<Production>> = HashMap::new();
    let mut parser_state = ParserState::new();
    let mut parser_name = None;
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
        Ok(ParsedLine::Name(name)) => match parser_name {
          Some(_) => {
            abort!(name.span, "Cannot have more than one parser name.");
          }
          None => {
            parser_name = Some(name);
          }
        },
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

    if parser_name.is_none() {
      abort!(
        Span::call_site(),
        "Must give a name with a line \"name: <name>;\""
      )
    }
    if terminal_type.is_none() {
      abort!(
        Span::call_site(),
        "Must define the terminal type with a line \"terminal: <type>;\""
      );
    }
    let parser_name = parser_name.unwrap();
    let terminal_type = terminal_type.unwrap();

    let mut grammar = Self {
      productions,
      start_rule: "".to_string(),
      parser_name,
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

        new_rules_list.push(ProductionRules::new(
          new_rule_list,
          prod.constructor.clone(),
          prod.span(),
        ));
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
    write!(f, "name: {}\n", self.parser_name)?;
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
