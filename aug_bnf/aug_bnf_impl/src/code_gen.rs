use quote::quote;

use crate::lr_table::{Action, LRState, LRTable};
use crate::production::{Grammar, ProductionRule};

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

  fn to_enum_variant_no_prefix(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
    let lr_state_name = syn::Ident::new(
      &format!("S{}", lr_state.uid),
      proc_macro2::Span::call_site(),
    );

    let state = match lr_state.last_sym() {
      Some(ProductionRule::Intermediate(prod)) => Some(prod.deref().name.type_spec_as_type()),
      Some(ProductionRule::Terminal(_term)) => Some(self.terminal_type.clone()),
      None => None,
    };

    if state.is_some() {
      let state = state.unwrap();
      quote! {
        #lr_state_name(#state)
      }
    } else {
      quote! {
        #lr_state_name
      }
    }
  }

  fn to_enum_variant(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
    let dfa_name = &self.dfa_name;
    let lr_state_name = self.to_enum_variant_no_prefix(lr_state);
    quote! {
      #dfa_name :: #lr_state_name
    }
  }

  fn to_enum_inst(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
    let dfa_name = &self.dfa_name;
    let lr_state_name = syn::Ident::new(
      &format!("S{}", lr_state.uid),
      proc_macro2::Span::call_site(),
    );
    quote! {
      #dfa_name :: #lr_state_name
    }
  }

  fn unique_var(uid: usize) -> proc_macro2::TokenStream {
    let ident = syn::Ident::new(&format!("v{}", uid), proc_macro2::Span::call_site());
    quote! {
      #ident
    }
  }

  fn generate_dfa_states(&self) -> proc_macro2::TokenStream {
    self
      .lr_table
      .states
      .iter()
      .fold(proc_macro2::TokenStream::new(), |tokens, lr_entry| {
        let lr_state = lr_entry.lr_state();
        let dfa_state = self.to_enum_variant_no_prefix(lr_state);
        quote! {
          #dfa_state,
          #tokens
        }
      })
  }

  fn generate_dfa_transitions(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
    let enum_variant = self.to_enum_variant(lr_state);

    lr_state.transitions.action_map.iter().fold(
      proc_macro2::TokenStream::new(),
      |tokens, (term, action)| {
        let term_pattern = term.as_peek_pattern();

        match action {
          Action::Shift(lr_table_entry) => {
            let next_lr_state = lr_table_entry.lr_state();
            let next_state = self.to_enum_inst(next_lr_state);
            let sym_tokens = term.as_sym_tokens();

            quote! {
              #tokens
              (#enum_variant, #term_pattern) => {
                println!("Consuming {}", #sym_tokens);
                // Consume the token.
                input_stream.next();
                states.push(#next_state(#sym_tokens));
              }
            }
          }
          Action::Reduce(prod_rule_ref) => {
            let rules = &prod_rule_ref.rules().rules;
            let mut parent_states = lr_state.parent_states.clone();

            let var_builders = rules.iter().enumerate().rev().fold(
              proc_macro2::TokenStream::new(),
              |tokens, (rule_idx, prod_rule)| {
                let var_name = Self::unique_var(rule_idx);
                parent_states = LRState::parents_of(&parent_states);

                // TODO next: figure out which enum variant this should be
                let val_extraction_assignment = if parent_states
                  .iter()
                  .all(|lr_state| lr_state.lr_state().is_initial_state())
                {
                  quote! {}
                } else {
                  let variants = parent_states.iter().fold(
                    proc_macro2::TokenStream::new(),
                    |tokens, lr_state| {
                      let lr_state = lr_state.lr_state();
                      let enum_inst = self.to_enum_inst(lr_state);

                      quote! {
                        #tokens
                        #enum_inst(val) => val,
                      }
                    },
                  );

                  quote! {
                    let #var_name = match states.pop() {
                      #variants
                      _ => unreachable!(),
                    };
                  }
                };

                match prod_rule {
                  ProductionRule::Intermediate(prod_ref) => {
                    let prod = prod_ref.deref();

                    // The type of values returned by constructors of this
                    // production.
                    let val_type = prod.name.type_spec_as_type();
                  }
                  ProductionRule::Terminal(term) => {
                    // TODO capture terminals too, either with $<index> or aliases
                  }
                }

                quote! {
                  #tokens
                  #val_extraction_assignment
                }
              },
            );

            // TODO: get from prod_rule_ref to prod_ref, push the goto state
            // let goto_state = lr_state.transitions.goto_map.get();

            quote! {
              #tokens
              (#enum_variant, #term_pattern) => {
                println!("Got to this guy!");
                #var_builders
                return None;
              }
            }
          }
        }
      },
    )
  }

  fn generate_match_loop(&self) -> proc_macro2::TokenStream {
    let initial_state = self.to_enum_variant(self.lr_table.initial_state.lr_state());
    let state_transitions =
      self
        .lr_table
        .states
        .iter()
        .fold(proc_macro2::TokenStream::new(), |tokens, lr_entry| {
          let lr_state = lr_entry.lr_state();
          let dfa_state = self.generate_dfa_transitions(lr_state);
          quote! {
            #dfa_state,
            #tokens
          }
        });

    quote! {
      let mut states = vec![#initial_state];
      loop {
        let state = states.last().unwrap();
        let next_token = input_stream.peek();

        match (state, next_token) {
          #state_transitions
          _ => {
            match next_token {
              Some(token) => {
                eprintln!("Unexpected token \"{}\"", token);
              }
              None => {
                eprintln!("Unexpected end of input");
              }
            }
            return None;
          }
        }
      }
    }
  }

  fn generate(&self) -> proc_macro2::TokenStream {
    let parser_name = &self.parser_name;
    let dfa_name = &self.dfa_name;
    let terminal_type = &self.terminal_type;
    let root_type = &self.root_type;

    let states = self.generate_dfa_states();
    let match_loop = self.generate_match_loop();

    quote! {
      enum #dfa_name {
        #states
      }

      struct #parser_name {}

      impl #parser_name {
        /// Parses an input stream according to the grammar, returning the
        /// constructed object from a correctly formatted input, or None if the
        /// input was not a sentential form of the grammar.
        pub fn parse<'a, I: Iterator<Item = &'a #terminal_type>>(mut input_stream: I) -> Option<#root_type> {
          let mut input_stream = input_stream.peekable();

          #match_loop
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
