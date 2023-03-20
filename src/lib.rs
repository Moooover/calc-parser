pub use parser_generator_impl::grammar_def;

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

  /// Asserts the result of a parse expression is some value and that the whole
  /// input is consumed.
  macro_rules! assert_full_evaluates {
    ($parse_result:expr, $expected_val:expr) => {
      if let Some((val, mut iter)) = $parse_result {
        assert_eq!(val, $expected_val);
        assert!(iter.peek().is_none());
      } else {
        assert!(false);
      }
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
    <V>: u32 => '2' { 2 } | '3' { 3 };
  }

  #[test]
  fn test_add_mul_single_digit() {
    assert_full_evaluates!(AddMul::parse(char_iter!("2")), 2);
  }

  #[test]
  fn test_add_mul_add() {
    assert_full_evaluates!(AddMul::parse(char_iter!("2+3")), 5);
  }

  #[test]
  fn test_add_mul_mul() {
    assert_full_evaluates!(AddMul::parse(char_iter!("2*3")), 6);
  }

  #[test]
  fn test_add_mul_mul_add() {
    assert_full_evaluates!(AddMul::parse(char_iter!("2*2+3")), 7);
  }

  #[test]
  fn test_add_mul_add_mul() {
    assert_full_evaluates!(AddMul::parse(char_iter!("2+2*3")), 8);
  }

  #[derive(Debug, PartialEq, Eq)]
  enum RequestType {
    GET,
    HEAD,
  }

  #[derive(Debug, PartialEq, Eq)]
  struct Req {
    req_type: RequestType,
    uri: String,
  }

  impl Req {
    pub fn new(req_type: RequestType, uri: String) -> Self {
      Self { req_type, uri }
    }
  }

  parser_generator_impl::grammar_def! {
    name: GetReq;
    terminal: char;

    // if no {} given, return entire consumed text.
    // a re before text means to treat the text as regex.
    <absoluteURI>: String => ':' <alphas> {
      #1.to_string() + &#alphas
    };
    <req>: RequestType => 'G' 'E' 'T' { RequestType::GET }
          | 'H' 'E' 'A' 'D' { RequestType::HEAD };
    <uri>: String => <absoluteURI> {
      #1
    };
    <header>: Req => <req> ' ' <uri> {
      Req::new(#req, #uri)
    };

    <alphas>: String => <alphas> <alpha> {
      #alphas + &#alpha.to_string()
    } | <alpha> {
      #alpha.to_string()
    };
    <alpha>: char => 'a' { 'a' } | 'b' { 'b' };
    // <alpha>: char => 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j'
    //          | 'k' | 'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't'
    //          | 'u' | 'v' | 'w' | 'x' | 'y' | 'z'
    //          | 'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J'
    //          | 'K' | 'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T'
    //          | 'U' | 'V' | 'W' | 'X' | 'Y' | 'Z';
  }

  #[test]
  fn test_parse_uri() {
    assert_full_evaluates!(
      GetReq::parse(char_iter!("GET :abba")),
      Req::new(RequestType::GET, ":abba".to_string())
    );
  }
}
