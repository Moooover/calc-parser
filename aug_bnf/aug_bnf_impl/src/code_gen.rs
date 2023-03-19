use quote::{quote, ToTokens};

use crate::lr_table::{Action, LRState, LRTable, LRTableEntry};
use crate::production::{Constructor, Grammar, ProductionRule, ProductionRules};
use crate::util::{ParseError, ParseResult};
use std::collections::HashMap;
use std::rc::Rc;

macro_rules! token_stream_with_span {
  ($stream:expr, $span:expr) => {
    proc_macro2::TokenStream::from_iter($stream.clone().into_iter().map(|mut token_tree| {
      token_tree.set_span($span);
      token_tree
    }))
  };
}

fn as_integer_literal(tokens: proc_macro2::TokenStream) -> Option<u32> {
  match syn::parse2::<syn::Lit>(tokens) {
    Ok(syn::Lit::Int(x)) => {
      if let Result::Ok(x) = x.base10_parse::<u32>() {
        Some(x)
      } else {
        None
      }
    }
    _ => None,
  }
}

struct ConstructorContext {
  var_idx_map: Vec<proc_macro2::TokenStream>,
  var_alias_map: HashMap<String, proc_macro2::TokenStream>,
}

impl ConstructorContext {
  fn from_rules<F: Fn(usize) -> proc_macro2::TokenStream>(
    prod_rules: &ProductionRules,
    var_generator: F,
  ) -> Self {
    let mut var_idx_map = Vec::new();
    let mut var_alias_map = HashMap::new();

    for (rule_idx, prod_rule) in prod_rules.rules.iter().enumerate() {
      let var_name = var_generator(rule_idx);

      // All rules may be captured via indexes.
      var_idx_map.push(var_name.clone());
      match prod_rule {
        ProductionRule::Intermediate(prod_ref) => {
          let prod = prod_ref.deref();

          // The type of values returned by constructors of this
          // production.
          let val_type = prod.name.type_spec_as_type();

          let var_ref = if let Some(alias) = &prod_ref.alias {
            alias.clone()
          } else {
            prod.name().to_string()
          };
          var_alias_map.insert(var_ref, var_name.clone());
        }
        ProductionRule::Terminal(term) => {
          // TODO also capture terminals with aliases, not just indexes.
        }
      }
    }

    Self {
      var_idx_map,
      var_alias_map,
    }
  }

  fn generate_constructor(
    &self,
    constructor: &Constructor,
  ) -> ParseResult<proc_macro2::TokenStream> {
    let input_tokens: proc_macro2::TokenStream = constructor.group.stream().into();
    let mut tokens_iter = input_tokens.into_iter().peekable();
    let mut cons_tokens = proc_macro2::TokenStream::new();
    while let Some(tt) = tokens_iter.next() {
      let mut to_insert = tt.to_token_stream();

      if let proc_macro2::TokenTree::Punct(p) = &tt {
        if p.as_char() == '#' && p.spacing() == proc_macro2::Spacing::Alone {
          if let Some(proc_macro2::TokenTree::Ident(sym)) = tokens_iter.peek() {
            if let Some(var_ref) = self.var_alias_map.get(&sym.to_string()) {
              to_insert = token_stream_with_span!(var_ref, sym.span());

              // Consume the identifier.
              tokens_iter.next();
            }
          } else if let Some(proc_macro2::TokenTree::Literal(literal)) = tokens_iter.peek() {
            if let Some(rule_num) = as_integer_literal(literal.to_token_stream()) {
              if rule_num < 1 || (rule_num as usize) > self.var_idx_map.len() {
                return ParseError::new(
                  &format!("Invalid rule number \"{}\"", rule_num),
                  tt.span().unwrap(),
                )
                .into();
              }
              // We already did the bounds check above!
              let var_ref = unsafe { self.var_idx_map.get_unchecked((rule_num - 1) as usize) };
              to_insert = token_stream_with_span!(var_ref, literal.span());

              // Consume the literal.
              tokens_iter.next();
            }
          }
        }
      }

      cons_tokens = quote! {
        #cons_tokens
        #to_insert
      }
    }

    return ParseResult::Ok(quote! {
      {
        #cons_tokens
      }
    });
  }
}

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

  fn to_enum_variant_typed_no_prefix(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
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

  fn to_enum_variant_no_prefix(&self, lr_state: &LRState) -> proc_macro2::TokenStream {
    let lr_state_name = syn::Ident::new(
      &format!("S{}", lr_state.uid),
      proc_macro2::Span::call_site(),
    );

    if lr_state.last_sym().is_some() {
      quote! {
        #lr_state_name(_)
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
        let dfa_state = self.to_enum_variant_typed_no_prefix(lr_state);
        quote! {
          #dfa_state,
          #tokens
        }
      })
  }

  fn generate_dfa_transitions(
    &self,
    lr_entry: &Rc<LRTableEntry>,
  ) -> ParseResult<proc_macro2::TokenStream> {
    let lr_state = lr_entry.lr_state();
    let enum_variant = self.to_enum_variant(lr_state);

    eprintln!("{}: {lr_state} ({enum_variant})", enum_variant.to_string());

    lr_state.transitions.action_map.iter().try_fold(
      proc_macro2::TokenStream::new(),
      |tokens, (term, action)| {
        let term_pattern = term.as_peek_pattern();

        match action {
          Action::Shift(lr_table_entry) => {
            let next_lr_state = lr_table_entry.lr_state();
            let next_state = self.to_enum_inst(next_lr_state);
            let sym_tokens = term.as_sym_tokens();

            ParseResult::Ok(quote! {
              #tokens
              (#enum_variant, #term_pattern) => {
                println!("Consuming {}", #sym_tokens);
                // Consume the token.
                input_stream.next();
                states.push(#next_state(#sym_tokens));
              }
            })
          }
          Action::Reduce(prod_rule_ref) | Action::Terminate(prod_rule_ref) => {
            let rules = &prod_rule_ref.rules().rules;
            let mut parent_states = LRTableEntry::as_parent_set(lr_entry);

            let cons_ctx = ConstructorContext::from_rules(prod_rule_ref.rules(), Self::unique_var);

            // For each of the states consumed by this rule, place them in a
            // unique variable indexed by the rule index corresponding to the
            // state consumed.
            let var_builders = rules.iter().enumerate().rev().fold(
              proc_macro2::TokenStream::new(),
              |tokens, (rule_idx, prod_rule)| {
                let var_name = Self::unique_var(rule_idx);
                let var_str = var_name.to_string();

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
                        Some(#enum_inst(val)) => val,
                      }
                    });

                parent_states = LRState::parents_of(&parent_states);

                quote! {
                  #tokens
                  let #var_name = match states.pop() {
                    #variants
                    _ => unreachable!(),
                  };
                  println!("Set {} to {:?}", #var_str, #var_name);
                }
              },
            );

            // Construct either the goto switch, or the return statement if
            // this is the initial state being completed.
            let goto_or_return = if let Action::Terminate(_) = action {
              // If this is a terminate action, then we can return the
              // constructed value, if the input stream is empty.
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
                  let evstr = next_enum_variant.to_string();

                  quote! {
                    #tokens
                    Some(#parent_enum_variant) => {
                      println!("Going to {}", #evstr);
                      states.push(#next_enum_variant(cons));
                    }
                  }
                },
              );

              quote! {
                match states.last() {
                  #goto_transitions
                  _ => unreachable!(),
                }
              }
            };

            let prod_rules = lr_state
              .states
              .states
              .iter()
              .nth(0)
              .unwrap()
              .inst
              .rule_ref
              .rules();
            let constructor = prod_rules.constructor.clone().unwrap_or_default();
            let cons_tokens = cons_ctx.generate_constructor(&constructor)?;

            eprintln!("{}", goto_or_return.to_string());
            eprintln!("cons: {}", constructor);

            ParseResult::Ok(quote! {
              #tokens
              (#enum_variant, #term_pattern) => {
                println!("Got to this guy!");
                #var_builders

                // TODO construct the variant
                let cons = #cons_tokens;

                #goto_or_return
              }
            })
          }
        }
        .into()
      },
    )
  }

  fn generate_match_loop(&self) -> ParseResult<proc_macro2::TokenStream> {
    let initial_state = self.to_enum_variant(self.lr_table.initial_state.lr_state());
    let state_transitions = self.lr_table.states.iter().try_fold(
      proc_macro2::TokenStream::new(),
      |tokens, lr_entry| {
        let dfa_state = self.generate_dfa_transitions(lr_entry)?;
        ParseResult::Ok(quote! {
          #dfa_state,
          #tokens
        })
      },
    )?;

    ParseResult::Ok(quote! {
      let mut states = vec![#initial_state];
      loop {
        let state = states.last().unwrap();
        let next_token = input_stream.peek();

        for s in states.iter() {
          print!("{:?} ", s);
        }
        println!("");
        println!("Matching ({:?}, {:?})", state, next_token);

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
    })
  }

  fn generate(&self) -> ParseResult<proc_macro2::TokenStream> {
    let parser_name = &self.parser_name;
    let dfa_name = &self.dfa_name;
    let terminal_type = &self.terminal_type;
    let root_type = &self.root_type;

    let states = self.generate_dfa_states();
    let match_loop = self.generate_match_loop()?;

    ParseResult::Ok(quote! {
      #[derive(Debug)]
      enum #dfa_name {
        #states
      }

      struct #parser_name {}

      impl #parser_name {
        /// Parses an input stream according to the grammar, returning the
        /// constructed object from a correctly formatted input, or None if the
        /// input was not a sentential form of the grammar.
        pub fn parse_ref<'a, I: Iterator<Item = &'a #terminal_type>>(mut input_stream: I) -> Option<#root_type> {
          let mut input_stream = input_stream.peekable();

          #match_loop
        }

        pub fn parse<I: Iterator<Item = #terminal_type>>(mut input_stream: I) -> Option<#root_type> {
          let mut input_stream = input_stream.peekable();

          #match_loop
        }
      }
    })
  }
}

pub fn to_match_loop(
  grammar: &Grammar,
  lr_table: &LRTable,
) -> ParseResult<proc_macro2::TokenStream> {
  CodeGen::new(grammar, lr_table).generate()
}
