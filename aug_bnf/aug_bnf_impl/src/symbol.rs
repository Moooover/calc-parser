use proc_macro::TokenTree::{Group, Ident, Literal, Punct};
use proc_macro::{Delimiter, Span, TokenStream};
use proc_macro_error::abort;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq, Eq)]
pub enum Operator {
  // =>
  Arrow,
  // :
  Colon,
  // ;
  Semicolon,
  // $
  DollarSign,
  // <
  BeginProd,
  // >
  EndProd,
  // ::
  Scope,
}

impl Operator {
  pub fn to_string(&self) -> &'static str {
    match self {
      Operator::Arrow => "=>",
      Operator::Colon => ":",
      Operator::Semicolon => ";",
      Operator::DollarSign => "$",
      Operator::BeginProd => "<",
      Operator::EndProd => ">",
      Operator::Scope => "::",
    }
  }
}

impl Operator {
  pub fn should_separate(prev_chars: &str, next_char: char) -> bool {
    let mut chars = prev_chars.chars();
    match chars.next() {
      Some(':') => chars.next().is_some() || next_char != ':',
      Some('=') => chars.next().is_some() || next_char != '>',
      Some(_) => true,
      None => true,
    }
  }
}

impl Display for Operator {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.to_string())
  }
}

pub enum SymbolT {
  // Operators are any special symbol, listed above.
  Op(Operator),
  // Identifiers are anything matching [a-zA-Z_]+
  Ident(String),
  // Literals are things that can only be terminals, like single-quote strings
  // (chars). Ident's may also be terminals, depending on what is being parsed.
  Literal(String),
  // Groups are the blocks of code to execute in successful matches.
  Group(TokenStream),
}

pub struct Symbol {
  pub sym: SymbolT,
  pub span: Span,
}

impl Symbol {
  pub fn new(sym: SymbolT, span: Span) -> Self {
    Self { sym, span }
  }

  fn is_ident_char(c: char) -> bool {
    return char::is_alphabetic(c) || c == '_';
  }

  fn parse_ident(input: &str, span: Span) -> Self {
    if input.chars().all(Self::is_ident_char) {
      return Symbol::new(SymbolT::Ident(input.to_string()), span);
    } else {
      abort!(span, format!("Unrecognized identifier: {}", input));
    }
  }

  fn parse_literal(input: &str, span: Span) -> Self {
    if input.chars().nth(0) == Some('\'') {
      return Symbol::new(SymbolT::Literal(input.to_string()), span);
    }
    if input.chars().all(Self::is_ident_char) {
      return Symbol::new(SymbolT::Ident(input.to_string()), span);
    } else {
      abort!(span, format!("Unrecognized literal: {}", input));
    }
  }

  fn parse_op(input: &str, span: Span) -> Self {
    match input {
      "=>" => Symbol::new(SymbolT::Op(Operator::Arrow), span),
      ":" => Symbol::new(SymbolT::Op(Operator::Colon), span),
      ";" => Symbol::new(SymbolT::Op(Operator::Semicolon), span),
      "$" => Symbol::new(SymbolT::Op(Operator::DollarSign), span),
      "<" => Symbol::new(SymbolT::Op(Operator::BeginProd), span),
      ">" => Symbol::new(SymbolT::Op(Operator::EndProd), span),
      "::" => Symbol::new(SymbolT::Op(Operator::Scope), span),
      _ => abort!(span, format!("Unrecognized operator: {}", input)),
    }
  }

  pub fn from_stream(tokens: TokenStream) -> Vec<Self> {
    let (list, _prev_chars) = tokens.into_iter().fold(
      (Vec::new(), None),
      |(mut syms, prev_chars), token| match &token {
        Group(group) => {
          if group.delimiter() == Delimiter::Brace {
            syms.push(Symbol::new(SymbolT::Group(group.stream()), group.span()));
            return (syms, None);
          } else {
            abort!(
              group.span_open(),
              format!(
                "Unrecognized token \"{}\"",
                match group.delimiter() {
                  Delimiter::Brace => "{",
                  Delimiter::Bracket => "[",
                  Delimiter::Parenthesis => "(",
                  Delimiter::None => "None",
                }
              )
            )
          }
        }
        Ident(ident) => {
          syms.push(Symbol::parse_ident(&ident.to_string(), token.span()));
          return (syms, None);
        }
        Literal(literal) => {
          syms.push(Symbol::parse_literal(&literal.to_string(), token.span()));
          return (syms, None);
        }
        Punct(punct) => {
          let prev_chars: (String, Option<Span>) = prev_chars.unwrap_or(("".to_string(), None));
          let (mut cur_chars, prev_span) = prev_chars;

          let cur_span = match prev_span {
            Some(span) => {
              if Operator::should_separate(&cur_chars, punct.as_char()) {
                syms.push(Symbol::parse_op(&cur_chars, span));
                cur_chars = "".to_string();
                token.span()
              } else {
                span.join(token.span()).unwrap()
              }
            }
            None => token.span(),
          };
          cur_chars += &String::from(punct.as_char());

          if punct.spacing() == proc_macro::Spacing::Joint {
            // There will be a character following this.
            return (syms, Some((cur_chars, Some(cur_span))));
          } else {
            // This is the last character in the punct.
            syms.push(Symbol::parse_op(&cur_chars, cur_span));
            return (syms, None);
          }
        }
      },
    );

    return list;
  }
}

impl Display for Symbol {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match &self.sym {
      SymbolT::Op(op) => write!(f, "{:?}", op),
      SymbolT::Ident(ident) => write!(f, "<{}>", ident),
      SymbolT::Group(token_stream) => write!(f, "{}", token_stream),
      SymbolT::Literal(token_stream) => write!(f, "{:?}", token_stream),
    }
  }
}
