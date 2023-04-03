#![feature(get_mut_unchecked, proc_macro_span)]

extern crate proc_macro;
mod code_gen;
mod lr_table_builder;
mod production;
mod symbol;
mod util;

use lr_table_builder::LRTable;
use proc_macro::TokenStream;
use proc_macro_error::proc_macro_error;
use production::Grammar;
// use quote::{quote, quote_spanned};
use symbol::Symbol;

#[proc_macro_error]
#[proc_macro]
/// Constructs an LR(1) parser based on the definition provided.
pub fn grammar_def(tokens: TokenStream) -> TokenStream {
  eprintln!("tokenizing");
  let list = Symbol::from_stream(tokens);
  eprintln!("parsing");
  let grammar = Grammar::from(list);
  eprintln!("gen lr table");
  let lr_table = LRTable::from_grammar(&grammar).unwrap_or_else(|err| err.raise());
  eprintln!("code gen");
  // eprintln!("{}", lr_table);
  let syn_tree = code_gen::to_match_loop(&grammar, &lr_table).unwrap_or_else(|err| err.raise());
  eprintln!("done");
  return syn_tree.into();
}
