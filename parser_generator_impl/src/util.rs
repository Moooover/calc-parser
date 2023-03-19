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
