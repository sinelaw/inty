//! Lexer module for tokenizing mquickjs JavaScript source code.

mod scanner;
mod token;

pub use scanner::Scanner;
pub use token::{Span, Spanned, Token};
