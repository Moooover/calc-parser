/// Constructs an AugBnf parser based on the definition provided.
pub use aug_bnf_impl::aug_bnf;

pub fn test_fn() {
  aug_bnf!(
    fn answer() -> i32 {
      43 | 32
    }
  );
  let result = bnswer();
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
