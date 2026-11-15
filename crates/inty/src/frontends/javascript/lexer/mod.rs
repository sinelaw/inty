//! Lexer module for tokenizing mquickjs JavaScript source code.

mod doc_annotation;
pub(crate) use doc_annotation::clean_doc_body;
mod scanner;
mod token;

pub use scanner::Scanner;
pub use token::{Span, Spanned, Token};
