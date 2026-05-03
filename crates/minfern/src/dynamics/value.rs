//! Runtime values for the operational semantics.
//!
//! Values are the things expressions reduce to. They are intentionally
//! distinct from `crate::types::Type`: types are static descriptions,
//! values are runtime data. The boundary matches the type-level / term-
//! level split in the design doc.
//!
//! Heap-allocated state (objects, arrays, mutable variable cells) lives
//! in `crate::dynamics::heap`; values that point at it carry a `Loc`.

use std::fmt;

use crate::parser::ast::Stmt;

use super::env::RuntimeEnv;
use super::heap::Loc;

/// A runtime value.
#[derive(Clone, Debug)]
pub enum Value {
    Number(f64),
    String(String),
    Boolean(bool),
    Null,
    Undefined,
    /// A closure capturing its definition-time environment.
    Closure(Closure),
    /// A reference to a heap-allocated array.
    Array(Loc),
    /// A reference to a heap-allocated object.
    Object(Loc),
    /// `Promise<v>`. Modelled as a transparent wrapper for now —
    /// `await p` reduces to `p`'s inner value. See phase-3 notes.
    Promise(Box<Value>),
}

#[derive(Clone, Debug)]
pub struct Closure {
    pub name: Option<String>,
    pub params: Vec<String>,
    pub body: Box<Stmt>,
    pub env: RuntimeEnv,
}

impl Value {
    /// JavaScript `typeof` result.
    pub fn type_string(&self) -> &'static str {
        match self {
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Boolean(_) => "boolean",
            Value::Undefined => "undefined",
            Value::Null => "object",
            Value::Closure(_) => "function",
            Value::Array(_) | Value::Object(_) => "object",
            Value::Promise(_) => "object",
        }
    }

    /// JavaScript truthiness (used by `!`, `if`, `while`, `&&`, `||`).
    pub fn truthy(&self) -> bool {
        match self {
            Value::Number(n) => *n != 0.0 && !n.is_nan(),
            Value::String(s) => !s.is_empty(),
            Value::Boolean(b) => *b,
            Value::Null | Value::Undefined => false,
            Value::Closure(_) | Value::Array(_) | Value::Object(_) | Value::Promise(_) => true,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Null => write!(f, "null"),
            Value::Undefined => write!(f, "undefined"),
            Value::Closure(c) => match &c.name {
                Some(n) => write!(f, "<closure {}>", n),
                None => write!(f, "<closure>"),
            },
            Value::Array(l) => write!(f, "<array @{}>", l.0),
            Value::Object(l) => write!(f, "<object @{}>", l.0),
            Value::Promise(v) => write!(f, "<promise {}>", v),
        }
    }
}
