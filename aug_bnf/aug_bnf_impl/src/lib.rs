extern crate proc_macro;
use proc_macro::TokenStream;
use proc_macro::TokenTree::{self, Group, Ident, Literal, Punct};

#[proc_macro]
pub fn aug_bnf(tokens: TokenStream) -> TokenStream {
  TokenStream::from_iter(tokens.into_iter().map(|token_tree| match token_tree {
    Group(group) => TokenStream::from(TokenTree::from(proc_macro::Group::new(
      group.delimiter(),
      aug_bnf(group.stream()),
    ))),
    Ident(ident) => {
      let ident = if ident.to_string() == "answer" {
        proc_macro::Ident::new("bnswer", ident.span())
      } else {
        ident
      };
      TokenStream::from(TokenTree::from(ident))
    }
    Punct(punct) => {
      let punct = if punct.as_char() == '|' {
        proc_macro::Punct::new('+', proc_macro::Spacing::Alone)
      } else {
        punct
      };
      TokenStream::from(TokenTree::from(punct))
    }
    Literal(lit) => {
      let lit = if lit.to_string() == "43" {
        proc_macro::Literal::u32_suffixed(42)
      } else {
        lit
      };
      TokenStream::from(TokenTree::from(lit))
    }
  }))
}
