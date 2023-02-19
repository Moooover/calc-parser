/// Constructs an AugBnf parser based on the definition provided.
pub use aug_bnf_impl::aug_bnf;

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
  // let parser = aug_bnf!(
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
  use super::*;

  #[test]
  fn it_works() {
    aug_bnf_impl::aug_bnf! {
      terminal: char;
      <S> => <A> <B>;
      <A> => 'a' <B>;
      <B> => 'b';
    };
  }
}
