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
pub fn aug_bnf(tokens: TokenStream) -> TokenStream {
  let list = Symbol::from_stream(tokens);
  let grammar = Grammar::from(list);
  // let s = format!("{}", grammar);
  let lr_table = LRTable::from_grammar(&grammar).unwrap_or_else(|err| err.raise());
  // let l = format!("{}", lr_table);
  let syn_tree = code_gen::to_match_loop(&grammar, &lr_table);
  return syn_tree.into();

  // return TokenStream::from(quote! {
  //   let var1 = #s;
  //   let var2 = #l;
  //   println!("{}", var1);
  //   println!("{}", var2);
  // });

  // let token_stream = list.iter().map(|sym| {
  //   let s = format!("{}", sym);
  //   let p = quote_spanned!(sym.span.into()=>
  //     println!
  //   );
  //   quote! {
  //     #p("sym: {}", #s);
  //   }
  // });
}
