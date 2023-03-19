pub use parser_generator_impl::grammar_def;

// enum RequestType {
//   GET,
//   HEAD,
// }

// struct Req {
//   req_type: RequestType,
//   uri: String,
// }

// impl Req {
//   pub fn new(req_type: RequestType, uri: &str) -> Self {
//     Self {
//       req_type,
//       uri: uri.to_string()
//     }
//   }
// }

pub fn test_fn() {
  // let parser = grammar_def!(
  //   0
  //   // if no {} given, return entire consumed text.
  //   // a re before text means to treat the text as regex.
  //   absoluteURI = re":[a-zA-Z/]+";
  //   // an evaluable block may be given for each option of a |
  //   req = "GET" { Request::GET } | "HEAD" { Request::HEAD };
  //   // parameter names are by default $<position>.
  //   uri = absoluteURI {
  //     $1
  //   };
  //   // the root rule is determined via the dependency graph: only one rule may
  //   // not be referred to by any others, and it is the root.
  //   header = req uri {
  //     Req::new($1, $2)
  //   };
  // );
}

#[cfg(test)]
mod tests {
  macro_rules! char_iter {
    ($s:expr) => {
      $s.chars().into_iter().peekable()
    };
  }

  parser_generator_impl::grammar_def! {
    name: TestSimple;
    terminal: char;

    <S> => 'a';
  }

  #[test]
  fn test_simple_parses() {
    assert!(TestSimple::parse(char_iter!("a")).is_some());
  }

  #[test]
  fn test_simple_empty_input() {
    assert!(TestSimple::parse(char_iter!("")).is_none());
  }

  #[test]
  fn test_simple_incorrect_input() {
    assert!(TestSimple::parse(char_iter!("b")).is_none());
  }

  #[test]
  fn test_simple_extra_input() {
    assert!(TestSimple::parse(char_iter!("ab")).is_some());
  }

  parser_generator_impl::grammar_def! {
    name: AddMul;
    terminal: char;

    <S>: u32 => <A> { #A };
    <A>: u32 => <A> '+' <P> {
      #A + #P
    } | <P> {
      #P
    };
    <P>: u32 => <P> '*' <V> {
      #P * #V
    } | <V> {
      #V
    };
    <V>: u32 => '1' { 1 } | '2' { 2 };
  }

  #[test]
  fn add_mul_grammar() {
    assert!(TestSimple::parse(char_iter!("ab")).is_some());
  }
}
