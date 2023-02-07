/// Constructs an AugBnf parser based on the definition provided.
pub use aug_bnf_impl::aug_bnf;

enum RequestType {
  GET,
  HEAD,
}

struct Req {
  req_type: RequestType,
  uri: String,
}

impl Req {
  pub fn new(req_type: RequestType, uri: &str) -> Self {
    Self {
      req_type,
      uri
    }
  }
}

pub fn test_fn() {
  let parser = aug_bnf!(
    absoluteURI = re":[a-zA-Z/]+";
    req = "GET" { Request::GET } | "HEAD" { Request::HEAD };
    uri = absoluteURI {
      absoluteURI
    };
    header = req uri {
      Req::new(req, uri)
    };
  );
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn it_works() {
    aug_bnf!(
      fn answer() -> i32 {
        42
      }
    );
    let result = answer();
    assert_eq!(result, 42);
  }
}
