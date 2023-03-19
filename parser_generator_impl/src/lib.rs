#![feature(get_mut_unchecked, proc_macro_span)]

extern crate proc_macro;
mod code_gen;
mod lr_table;
mod production;
mod symbol;
mod util;

use lr_table::LRTable;
use proc_macro::TokenStream;
use proc_macro_error::proc_macro_error;
use production::Grammar;
// use quote::{quote, quote_spanned};
use symbol::Symbol;

#[proc_macro_error]
#[proc_macro]
/// Constructs an LR(1) parser based on the definition provided.
pub fn grammar_def(tokens: TokenStream) -> TokenStream {
  let list = Symbol::from_stream(tokens);
  let grammar = Grammar::from(list);
  let lr_table = LRTable::from_grammar(&grammar).unwrap_or_else(|err| err.raise());
  eprintln!("{}", lr_table);
  let syn_tree = code_gen::to_match_loop(&grammar, &lr_table).unwrap_or_else(|err| err.raise());
  return syn_tree.into();
}
