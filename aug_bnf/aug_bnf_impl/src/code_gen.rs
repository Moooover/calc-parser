use quote::quote;

use crate::lr_table::{Action, LRState, LRTable, LRTableEntry};
use crate::production::{Grammar, ProductionRule};
use std::rc::Rc;

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

  fn final_enum_variant_no_prefix(&self) -> proc_macro2::TokenStream {
    let table_result_type = self
      .lr_table
      .initial_state
      .lr_state()
      .states
      .states
      .iter()
      .nth(0)
      .unwrap()
      .inst
      .rule_ref
      .prod_ref()
      .deref()
      .name
      .type_spec_as_type();
    quote! { T(#table_result_type) }
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
    let final_state = self.final_enum_variant_no_prefix();
    let states = quote! {
      #final_state,
    };

    self
      .lr_table
      .states
      .iter()
      .fold(states, |tokens, lr_entry| {
        let lr_state = lr_entry.lr_state();
        let dfa_state = self.to_enum_variant_no_prefix(lr_state);
        quote! {
          #dfa_state,
          #tokens
        }
      })
  }

  fn generate_dfa_transitions(&self, lr_entry: &Rc<LRTableEntry>) -> proc_macro2::TokenStream {
    let lr_state = lr_entry.lr_state();
    let enum_variant = self.to_enum_variant(lr_state);

    eprintln!("state: {} ({})", lr_state, enum_variant);

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
            let mut parent_states = LRTableEntry::as_parent_set(lr_entry);

            // For each of the states consumed by this rule, place them in a
            // unique variable indexed by the rule index corresponding to the
            // state consumed.
            let var_builders = rules.iter().enumerate().rev().fold(
              proc_macro2::TokenStream::new(),
              |tokens, (rule_idx, prod_rule)| {
                let var_name = Self::unique_var(rule_idx);
                let x = prod_rule.to_string();
                let y = prod_rule_ref.rules().to_string();

                // States can be reached via multiple paths through the dfa if
                // they or their ancestors were merged, so we need to match
                // against every possible state that each rule could have been
                // from.
                let variants =
                  parent_states
                    .iter()
                    .fold(proc_macro2::TokenStream::new(), |tokens, lr_state| {
                      let lr_state = lr_state.lr_state();
                      let enum_inst = self.to_enum_inst(lr_state);

                      quote! {
                        #tokens
                        Some(#enum_inst(val)) => {
                          println!("{}, {}", #x, #y);
                          val
                        }
                      }
                    });

                // match prod_rule {
                //   ProductionRule::Intermediate(prod_ref) => {
                //     let prod = prod_ref.deref();

                //     // The type of values returned by constructors of this
                //     // production.
                //     let val_type = prod.name.type_spec_as_type();
                //   }
                //   ProductionRule::Terminal(term) => {
                //     // TODO capture terminals too, either with $<index> or aliases
                //   }
                // }

                parent_states = LRState::parents_of(&parent_states);

                quote! {
                  #tokens
                  let #var_name = match states.pop() {
                    #variants
                    _ => unreachable!(),
                  };
                }
              },
            );

            // TODO: get from prod_rule_ref to prod_ref, push the goto state
            // let goto_state = lr_state.transitions.goto_map.get();

            // Construct either the goto switch, or the return statement if
            // this is the initial state being completed.
            let goto_or_return = if parent_states
              .iter()
              .all(|lr_entry_ptr| lr_entry_ptr.lr_state().is_initial_state())
            {
              // If all parent states are the initial state, then we can return
              // the constructed value, if the input stream is empty.
              quote! {
                if input_stream.peek().is_some() {
                  return None;
                }
                return Some(cons);
              }
            } else {
              let goto_transitions = parent_states.iter().fold(
                proc_macro2::TokenStream::new(),
                |tokens, lr_entry_ptr| {
                  let parent_lr_state = lr_entry_ptr.lr_state();
                  let parent_enum_variant = self.to_enum_variant(parent_lr_state);

                  let next_lr_entry_ptr = parent_lr_state
                    .transitions
                    .goto_map
                    .get(prod_rule_ref.prod_ref());
                  if next_lr_entry_ptr.is_none() {
                    // The only way there can exist no parent states is if this
                    // is the initial production rule, meaning we only have to
                    // check that the input stream is empty.
                    eprintln!(
                      "Ruh roh! {} => {} ({})",
                      lr_entry_ptr, lr_entry, prod_rule_ref
                    );
                    unreachable!();
                  }
                  let next_lr_state = next_lr_entry_ptr.unwrap().lr_state();
                  let next_enum_variant = self.to_enum_inst(next_lr_state);

                  quote! {
                    #tokens
                    Some(#parent_enum_variant) => {
                      states.push(#next_enum_variant(cons));
                    }
                  }
                },
              );

              quote! {
                match states.pop() {
                  #goto_transitions
                  _ => unreachable!(),
                }
              }
            };

            eprintln!("{}", goto_or_return.to_string());

            quote! {
              #tokens
              (#enum_variant, #term_pattern) => {
                println!("Got to this guy!");
                #var_builders

                // TODO construct the variant
                let cons = 0;

                #goto_or_return
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
          let dfa_state = self.generate_dfa_transitions(lr_entry);
          quote! {
            #dfa_state,
            #tokens
          }
        });
    eprintln!("{}", state_transitions.to_string());

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
  CodeGen::new(grammar, lr_table).generate()
}
