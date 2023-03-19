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
  // #
  NumberSign,
  // <
  BeginProd,
  // >
  EndProd,
  // |
  Pipe,
  // ::
  Scope,
  // !
  Bang,
  // Anything else
  Unknown,
}

impl Operator {
  pub fn to_string(&self) -> &'static str {
    match self {
      Operator::Arrow => "=>",
      Operator::Colon => ":",
      Operator::Semicolon => ";",
      Operator::NumberSign => "#",
      Operator::BeginProd => "<",
      Operator::EndProd => ">",
      Operator::Pipe => "!",
      Operator::Scope => "::",
      Operator::Bang => "!",
      Operator::Unknown => "?",
    }
  }
}

impl Operator {
  pub fn should_separate(prev_chars: &str, next_char: char) -> bool {
    let mut chars = prev_chars.chars();
    match chars.next() {
      Some('=') => chars.next().is_some() || next_char != '>',
      Some(';') => true,
      Some('#') => true,
      Some('<') => true,
      Some('>') => true,
      Some('|') => true,
      Some(':') => chars.next().is_some() || next_char != ':',
      Some('!') => true,
      Some(_) => false,
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
  Group(proc_macro::Group),
  // Tuples are blocks of code within parenthesis.
  Tuple(TokenStream),
  // Arrays are for array slice types, i.e. &[u64].
  Array(TokenStream),
}

pub struct Symbol {
  pub sym: SymbolT,
  pub span: Span,
  pub tokens: TokenStream,
}

impl Symbol {
  pub fn new(sym: SymbolT, span: Span, tokens: TokenStream) -> Self {
    Self { sym, span, tokens }
  }

  fn is_leading_ident_char(c: char) -> bool {
    return char::is_alphabetic(c) || c == '_';
  }

  fn is_ident_char(c: char) -> bool {
    return char::is_alphanumeric(c) || c == '_';
  }

  fn parse_ident(input: &str, span: Span, tokens: TokenStream) -> Self {
    if input.chars().all(Self::is_ident_char)
      && Self::is_leading_ident_char(input.chars().nth(0).unwrap())
    {
      return Symbol::new(SymbolT::Ident(input.to_string()), span, tokens);
    } else {
      abort!(span, format!("Unrecognized identifier: {}", input));
    }
  }

  fn parse_literal(input: &str, span: Span, tokens: TokenStream) -> Self {
    if input.chars().nth(0) == Some('\'') {
      return Symbol::new(SymbolT::Literal(input.to_string()), span, tokens);
    }
    if input.chars().all(Self::is_ident_char) {
      return Symbol::new(SymbolT::Ident(input.to_string()), span, tokens);
    } else {
      abort!(span, format!("Unrecognized literal: {}", input));
    }
  }

  fn parse_op(input: &str, span: Span, tokens: TokenStream) -> Self {
    match input {
      "=>" => Symbol::new(SymbolT::Op(Operator::Arrow), span, tokens),
      ":" => Symbol::new(SymbolT::Op(Operator::Colon), span, tokens),
      ";" => Symbol::new(SymbolT::Op(Operator::Semicolon), span, tokens),
      "#" => Symbol::new(SymbolT::Op(Operator::NumberSign), span, tokens),
      "<" => Symbol::new(SymbolT::Op(Operator::BeginProd), span, tokens),
      ">" => Symbol::new(SymbolT::Op(Operator::EndProd), span, tokens),
      "|" => Symbol::new(SymbolT::Op(Operator::Pipe), span, tokens),
      "::" => Symbol::new(SymbolT::Op(Operator::Scope), span, tokens),
      "!" => Symbol::new(SymbolT::Op(Operator::Bang), span, tokens),
      _ => Symbol::new(SymbolT::Op(Operator::Unknown), span, tokens),
    }
  }

  pub fn from_stream(tokens: TokenStream) -> Vec<Self> {
    let (list, _prev_chars, _prev_tokens) = tokens.into_iter().fold(
      (Vec::new(), None, None),
      |(mut syms, prev_chars, prev_tokens), token| match token.clone() {
        Group(group) => match group.delimiter() {
          Delimiter::Brace => {
            syms.push(Symbol::new(
              SymbolT::Group(group.clone()),
              group.span(),
              token.into(),
            ));
            return (syms, None, None);
          }
          Delimiter::Parenthesis => {
            syms.push(Symbol::new(
              SymbolT::Tuple(group.stream()),
              group.span(),
              token.into(),
            ));
            return (syms, None, None);
          }
          Delimiter::Bracket => {
            syms.push(Symbol::new(
              SymbolT::Array(group.stream()),
              group.span(),
              token.into(),
            ));
            return (syms, None, None);
          }
          _ => abort!(
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
          ),
        },
        Ident(ident) => {
          syms.push(Symbol::parse_ident(
            &ident.to_string(),
            token.span(),
            token.into(),
          ));
          return (syms, None, None);
        }
        Literal(literal) => {
          syms.push(Symbol::parse_literal(
            &literal.to_string(),
            token.span(),
            token.into(),
          ));
          return (syms, None, None);
        }
        Punct(punct) => {
          let prev_chars: (String, Option<Span>) = prev_chars.unwrap_or(("".to_string(), None));
          let (mut cur_chars, prev_span) = prev_chars;

          let (cur_span, cur_tokens) = match (prev_span, prev_tokens) {
            (Some(span), Some(mut tokens)) => {
              if Operator::should_separate(&cur_chars, punct.as_char()) {
                syms.push(Symbol::parse_op(&cur_chars, span, tokens));
                cur_chars = "".to_string();
                (token.span(), token.into())
              } else {
                tokens.extend(TokenStream::from(token.clone()));
                (span.join(token.span()).unwrap(), tokens)
              }
            }
            (None, None) => (token.span(), token.into()),
            _ => unreachable!(),
          };
          cur_chars += &String::from(punct.as_char());

          if punct.spacing() == proc_macro::Spacing::Joint {
            // There will be a character following this.
            return (syms, Some((cur_chars, Some(cur_span))), Some(cur_tokens));
          } else {
            // This is the last character in the punct.
            syms.push(Symbol::parse_op(&cur_chars, cur_span, cur_tokens));
            return (syms, None, None);
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
      SymbolT::Tuple(token_stream) => write!(f, "({})", token_stream),
      SymbolT::Array(token_stream) => write!(f, "[{}]", token_stream),
      SymbolT::Literal(token_stream) => write!(f, "{:?}", token_stream),
    }
  }
}
