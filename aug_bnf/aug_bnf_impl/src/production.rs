use proc_macro::Span;
use proc_macro_error::abort;
use std::collections::HashMap;
use std::iter::Peekable;

use crate::symbol::{Operator, Symbol, SymbolT};

#[derive(Debug, PartialEq, Eq)]
enum ParseErrorType {
  // End of stream was reached.
  EndOfStream,
  // An unexpected token was found.
  UnexpectedToken,
}

#[derive(Debug)]
struct ParseError {
  err_type: ParseErrorType,
  message: String,
  span: Span,
}

impl ParseError {
  pub fn new(err_type: ParseErrorType, message: &str, span: Span) -> Self {
    Self {
      err_type,
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
    return ParseError::new(ParseErrorType::EndOfStream, message, span).into();
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
    return ParseError::new(ParseErrorType::EndOfStream, message, span).into();
  }
}

macro_rules! expect_symbol {
  ($iter:expr, $expected:pat, $message:expr, $span:expr) => {
    let sym = next_symbol_or($iter, $message, $span)?;
    match sym.sym {
      $expected => {}
      _ => {
        return ParseError::new(ParseErrorType::UnexpectedToken, $message, sym.span).into();
      }
    }
  };
}

// <TerminalSym> => <Ident>
#[derive(Debug)]
struct TerminalSym {
  pub name: String,
  pub span: Span,
}

impl TerminalSym {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut T) -> ParseResult<Self> {
    let sym = next_symbol_or(iter, "Expected terminal symbol.", Span::call_site())?;

    match sym.sym {
      SymbolT::Ident(ident) => Ok(TerminalSym {
        name: ident,
        span: sym.span,
      }),
      SymbolT::Literal(literal) => Ok(TerminalSym {
        name: literal,
        span: sym.span,
      }),
      _ => ParseError::new(
        ParseErrorType::UnexpectedToken,
        "Expected terminal symbol.",
        sym.span,
      )
      .into(),
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
    expect_symbol!(
      iter,
      SymbolT::Op(Operator::BeginProd),
      "Expected production rule name, which must begin with a '<'.",
      Span::call_site()
    );

    let sym = next_symbol_or(iter, "Dangling '<'", Span::call_site())?;

    let production_name = match &sym.sym {
      SymbolT::Ident(ident) => ident.to_string(),
      _ => {
        return ParseError::new(
          ParseErrorType::UnexpectedToken,
          "Expected production rule name.",
          sym.span,
        )
        .into();
      }
    };

    expect_symbol!(
      iter,
      SymbolT::Op(Operator::EndProd),
      "Expected '>' at end of production rule name.",
      Span::call_site()
    );

    Ok(Self {
      name: production_name,
      // You can't alias the production definition.
      alias: None,
      span: sym.span,
    })
  }
}

// <ProductionRule> => <ProductionName> | <TerminalSym>
#[derive(Debug)]
enum ProductionRule<'a> {
  Intermediate(&'a Production<'a>),
  Terminal(TerminalSym),
  UnresolvedIntermediate(ProductionName),
}

impl<'a> ProductionRule<'a> {
  pub fn span(&self) -> Span {
    match self {
      Self::Intermediate(intermediate) => intermediate.span,
      Self::Terminal(terminal) => terminal.span,
      Self::UnresolvedIntermediate(name) => name.span,
    }
  }
}

impl<'a> ProductionRule<'a> {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

    match sym.sym {
      SymbolT::Op(Operator::BeginProd) => Ok(ProductionRule::UnresolvedIntermediate(
        ProductionName::parse(iter)?,
      )),
      _ => Ok(ProductionRule::Terminal(TerminalSym::parse(iter)?)),
    }
  }
}

// <ProductionRules> => <ProductionRule> <ProductionRules>?
#[derive(Debug)]
struct ProductionRules<'a> {
  pub rules: Vec<ProductionRule<'a>>,
  pub span: Span,
}

impl<'a> ProductionRules<'a> {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Vec<Self>> {
    let mut rules = Vec::new();
    let mut span = None;

    loop {
      let sym = peek_symbol_or(iter, "Unexpected end of stream.", Span::call_site())?;

      match sym.sym {
        SymbolT::Op(Operator::Semicolon) => {
          if rules.len() == 0 {
            return ParseError::new(
              ParseErrorType::UnexpectedToken,
              "Unexpected ';', expect production rule.",
              sym.span,
            )
            .into();
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

// <Production> => <ProductionName> "=>" <ProductionRules>
#[derive(Debug)]
struct Production<'a> {
  name: ProductionName,
  rules: Vec<ProductionRules<'a>>,
  span: Span,
}

impl<'a> Production<'a> {
  pub fn parse<T: Iterator<Item = Symbol>>(iter: &mut Peekable<T>) -> ParseResult<Self> {
    let production_name = ProductionName::parse(iter)?;

    expect_symbol!(
      iter,
      SymbolT::Op(Operator::Arrow),
      "Expected \"=>\" to follow production name.",
      production_name.span
    );

    let production_rules = ProductionRules::parse(iter)?;
    let span = production_name
      .span
      .join(iter_span(production_rules.iter().map(|rule| rule.span)))
      .unwrap();

    Ok(Self {
      name: production_name,
      rules: production_rules,
      span,
    })
  }
}

#[derive(Debug)]
pub struct Grammar<'a> {
  productions: HashMap<&'a str, Production<'a>>,
  start_rule: &'a str,
}

impl<'a> Grammar<'a> {
  pub fn from(token_stream: Vec<Symbol>) -> Self {
    let productions: HashMap<&'a str, Production<'a>> = HashMap::new();
    let start_rule: Option<&'a str> = Some("hi");

    let mut token_iter = token_stream.into_iter().peekable();
    while let Some(_) = token_iter.peek() {
      match Production::parse(&mut token_iter) {
        Ok(production) => {}
        Err(err) => {
          abort!(err.span, err.message);
        }
      }
    }

    Self {
      productions,
      start_rule: start_rule.unwrap(),
    }
  }
}
