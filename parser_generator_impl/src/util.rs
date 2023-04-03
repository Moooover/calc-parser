use std::{
  borrow::{Borrow, BorrowMut},
  fmt::{Debug, Display},
  hash::{Hash, Hasher},
  ops::{Deref, DerefMut},
};

use proc_macro::Span;
use proc_macro_error::abort;

#[derive(Debug)]
pub struct ParseError {
  message: String,
  span: Span,
}

impl ParseError {
  pub fn new(message: &str, span: Span) -> Self {
    Self {
      message: String::from(message),
      span,
    }
  }

  pub fn raise(&self) -> ! {
    abort!(self.span, self.message);
  }
}

impl<T> From<ParseError> for ParseResult<T> {
  fn from(parse_err: ParseError) -> ParseResult<T> {
    Err(parse_err)
  }
}

pub type ParseResult<T = ()> = Result<T, ParseError>;

pub struct Transparent<T> {
  data: T,
}

impl<T> Transparent<T> {
  pub fn data(self) -> T {
    self.data
  }
}

impl<T> Borrow<T> for Transparent<T> {
  fn borrow(&self) -> &T {
    &self.data
  }
}

impl<T> BorrowMut<T> for Transparent<T> {
  fn borrow_mut(&mut self) -> &mut T {
    &mut self.data
  }
}

impl<T: Clone> Clone for Transparent<T> {
  fn clone(&self) -> Self {
    self.data.clone().into()
  }
}

impl<T: Debug> Debug for Transparent<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Debug::fmt(&self.data, f)
  }
}

impl<T> Deref for Transparent<T> {
  type Target = T;

  fn deref(&self) -> &T {
    &self.data
  }
}

impl<T> DerefMut for Transparent<T> {
  fn deref_mut(&mut self) -> &mut T {
    &mut self.data
  }
}

impl<T: Display> Display for Transparent<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Display::fmt(&self.data, f)
  }
}

impl<T> From<T> for Transparent<T> {
  fn from(value: T) -> Self {
    Self { data: value }
  }
}

impl<T> Hash for Transparent<T> {
  fn hash<H: Hasher>(&self, _state: &mut H) {}
}

impl<T> PartialEq for Transparent<T> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<T> Eq for Transparent<T> {}

impl<T> PartialOrd for Transparent<T> {
  fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
    Some(std::cmp::Ordering::Equal)
  }
}

impl<T> Ord for Transparent<T> {
  fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
    std::cmp::Ordering::Equal
  }
}
