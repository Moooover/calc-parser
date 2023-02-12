#![feature(proc_macro_span)]

extern crate proc_macro;
use proc_macro::TokenTree::{Group, Ident, Literal, Punct};
use proc_macro::{Delimiter, Span, TokenStream};
use proc_macro_error::{abort, proc_macro_error};
use quote::{quote, quote_spanned};
use std::fmt::{Display, Formatter};

trait TerminalT: std::fmt::Debug + PartialEq + Eq {}

#[derive(Debug)]
enum Operator {
  // =>
  Arrow,
  // :
  Colon,
  // $
  VarPrefix,
}

enum SymbolT<T: TerminalT> {
  Op(Operator),
  Ident(String),
  Terminal(T),
  Group(TokenStream),
}

struct Symbol<T: TerminalT> {
  pub sym: SymbolT<T>,
  pub span: Span,
}

impl<T: TerminalT> Symbol<T> {
  pub fn new(sym: SymbolT<T>, span: Span) -> Self {
    Self { sym, span }
  }

  fn parse_ident(input: &str, span: Span) -> Option<Self> {
    if input.chars().all(char::is_alphabetic) {
      return Some(Symbol::new(SymbolT::Ident(input.to_string()), span));
    } else {
      return None;
    }
  }

  fn parse(input: &str, span: Span) -> Option<Self> {
    match input {
      "=>" => Some(Symbol::new(SymbolT::Op(Operator::Arrow), span)),
      ":" => Some(Symbol::new(SymbolT::Op(Operator::Colon), span)),
      "$" => Some(Symbol::new(SymbolT::Op(Operator::VarPrefix), span)),
      _ => Self::parse_ident(input, span),
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
          if let Some(sym) = Symbol::parse(&ident.to_string(), token.span()) {
            syms.push(sym);
            return (syms, None);
          } else {
            abort!(token.span(), format!("Unrecognized symbol \"{}\"", token));
          }
        }
        Literal(literal) => {
          if let Some(sym) = Symbol::parse(&literal.to_string(), token.span()) {
            syms.push(sym);
            return (syms, None);
          } else {
            abort!(token.span(), format!("Unrecognized symbol \"{}\"", token));
          }
        }
        Punct(punct) => {
          let prev_chars: (String, Option<Span>) = prev_chars.unwrap_or(("".to_string(), None));
          let (mut cur_chars, prev_span) = prev_chars;
          cur_chars += &String::from(punct.as_char());
          let cur_span = match prev_span {
            Some(span) => span.join(token.span()).unwrap(),
            None => token.span(),
          };

          if punct.spacing() == proc_macro::Spacing::Joint {
            // There will be a character following this.
            return (syms, Some((cur_chars, Some(cur_span))));
          } else {
            // This is the last character in the punct.
            if let Some(punct) = Symbol::parse(&cur_chars, cur_span) {
              syms.push(punct);
              return (syms, None);
            } else {
              abort!(cur_span, format!("Unrecognized operator \"{}\"", cur_chars));
            }
          }
        }
      },
    );

    return list;
  }
}

impl<T: TerminalT> Display for Symbol<T> {
  fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
    match &self.sym {
      SymbolT::Op(op) => write!(f, "{:?}", op),
      SymbolT::Ident(ident) => write!(f, "{}", ident),
      SymbolT::Group(token_stream) => write!(f, "{}", token_stream),
      SymbolT::Terminal(token_stream) => write!(f, "{:?}", token_stream),
    }
  }
}

impl TerminalT for char {}

#[proc_macro_error]
#[proc_macro]
pub fn aug_bnf(tokens: TokenStream) -> TokenStream {
  let list = Symbol::<char>::from_stream(tokens);
  let token_stream = list.iter().map(|sym| {
    let s = format!("{}", sym);
    let p = quote_spanned!(sym.span.into()=>
      println!
    );
    quote! {
      #p("sym: {}", #s);
    }
  });

  return TokenStream::from(
    token_stream
      .reduce(|mut res, token_stream| {
        res.extend(token_stream);
        res
      })
      .unwrap(),
  );
}

// #[proc_macro]
// pub fn aug_bnf(tokens: TokenStream) -> TokenStream {
//   TokenStream::from_iter(tokens.into_iter().map(|token_tree| match token_tree {
//     Group(group) => TokenStream::from(TokenTree::from(proc_macro::Group::new(
//       group.delimiter(),
//       aug_bnf(group.stream()),
//     ))),
//     Ident(ident) => {
//       let ident = if ident.to_string() == "answer" {
//         proc_macro::Ident::new("bnswer", ident.span())
//       } else {
//         ident
//       };
//       TokenStream::from(TokenTree::from(ident))
//     }
//     Punct(punct) => {
//       let punct = if punct.as_char() == '|' {
//         proc_macro::Punct::new('+', proc_macro::Spacing::Alone)
//       } else {
//         punct
//       };
//       TokenStream::from(TokenTree::from(punct))
//     }
//     Literal(lit) => {
//       let lit = if lit.to_string() == "43" {
//         proc_macro::Literal::u32_suffixed(42)
//       } else {
//         lit
//       };
//       TokenStream::from(TokenTree::from(lit))
//     }
//   }))
// }
