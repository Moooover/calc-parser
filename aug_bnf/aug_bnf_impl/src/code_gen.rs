use quote::quote;

use crate::lr_table::{LRState, LRTable};
use crate::production::Grammar;

struct CodeGen<'a> {
  grammar: &'a Grammar,
  lr_table: &'a LRTable,

  parser_name: syn::Ident,
  dfa_name: syn::Ident,
  terminal_type: syn::Type,
  root_type: syn::Type,
}

impl<'a> CodeGen<'a> {
  fn new(grammar: &'a Grammar, lr_table: &'a LRTable) -> Self {
    let parser_name = grammar.parser_name.as_ident();
    let dfa_name = syn::Ident::new(
      &format!("{}DfaStates", grammar.parser_name.name.clone()),
      grammar.parser_name.span.into(),
    );
    let terminal_type = grammar.terminal_type.as_type();
    let root_type = grammar.starting_rule().deref().name.type_spec_as_type();

    Self {
      grammar,
      lr_table,
      parser_name,
      dfa_name,
      terminal_type,
      root_type,
    }
  }

  fn to_enum_variant(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
    let dfa_name = &self.dfa_name;
    let lr_state_name = syn::Ident::new(
      &format!("S{}", lr_state.uid),
      proc_macro2::Span::call_site(),
    );
    quote! {
      #dfa_name :: #lr_state_name
    }
  }

  fn generate_dfa_states(&self) -> proc_macro2::TokenStream {
    quote! {}
  }

  fn generate(&self) -> proc_macro2::TokenStream {
    let parser_name = &self.parser_name;
    let dfa_name = &self.dfa_name;
    let terminal_type = &self.terminal_type;
    let root_type = &self.root_type;

    eprintln!(
      "{:?}",
      self.to_enum_variant(self.lr_table.initial_state.lr_state())
    );

    quote! {
      enum #dfa_name {}

      struct #parser_name {}

      impl #parser_name {
        /// Parses an input stream according to the grammar, returning the
        /// constructed object from a correctly formatted input, or None if the
        /// input was not a sentential form of the grammar.
        pub fn parse<'a, I: Iterator<Item = &'a #terminal_type>>(input_stream: I) -> Option<#root_type> {
          for term in input_stream {
            println!("{}", term);
          }

          None
        }
      }
    }
  }
}

pub fn to_match_loop(grammar: &Grammar, lr_table: &LRTable) -> proc_macro2::TokenStream {
  // let l = format!("{}", lr_table);
  let code_gen = CodeGen::new(grammar, lr_table);

  return code_gen.generate();

  // 'outer: for lr_table_entry in &lr_table.states {
  //   for state in &lr_table_entry.state_builder_ref().states {
  //     v.push(format!("{}", state.inst.rule_ref));
  //     if state.inst.rule_ref.rules().constructor.as_ref().is_some() {
  //       let x: syn::Result<syn::ExprBlock> = parse(
  //         proc_macro::TokenTree::Group(
  //           state
  //             .inst
  //             .rule_ref
  //             .rules()
  //             .constructor
  //             .as_ref()
  //             .unwrap()
  //             .group
  //             .clone(),
  //         )
  //         .into(),
  //       );
  //     }
  //   }
  // }
}
