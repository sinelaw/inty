//! Iteration 0's model: a first-order slice of the operators of inty's
//! Lean model (`lean/Inty/Syntax.lean`): numbers, strings and booleans, `+`
//! on two numbers or two strings (inty's `Plus` class), `-` and `<` on
//! numbers, `===` and `typeof` on anything, string `.length`, and a
//! conditional on booleans. `model` is where the model grows; this stays as
//! the first-order fixture.
//!
//! Unlike JavaScript, and like the model, `1 + "a"` and `1 < "a"` are stuck.
//! So is `1 == "a"`: `==` compares values of one type (`===` any two), so
//! its operands' type may not be a union.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Core {
    sig: Vec<Con>,
}

const NUM: usize = 0;
const STR: usize = 1;
const TRUE: usize = 2;
const FALSE: usize = 3;
const PLUS: usize = 4;
const MINUS: usize = 5;
const LT: usize = 6;
const EQ: usize = 7;
const TYPEOF: usize = 8;
const LENGTH: usize = 9;
const IF: usize = 10;
const VAR: usize = 11;
const EQ_STRICT: usize = 12;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Num(i64),
    Str(String),
    Bool(bool),
}

impl Default for Core {
    fn default() -> Self {
        Core {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::literal("str", vec![Atom::Str(String::new()), Atom::Str("a".into())]),
                Con::op("true", 0),
                Con::op("false", 0),
                Con::op("+", 2),
                Con::op("-", 2),
                Con::op("<", 2),
                Con::op("===", 2),
                Con::op("typeof", 1),
                Con::op("length", 1),
                Con::op("if", 3),
                Con::var(),
                Con::op("==", 2),
            ],
        }
    }
}

impl Language for Core {
    type Value = Val;

    fn name(&self) -> &str {
        "core (a first-order slice of inty's Lean model)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        use Outcome::*;
        use Val::*;
        if t.con == VAR {
            return match t.atom {
                Atom::Int(i) if (i as usize) < env.len() => Value(env[i as usize].clone()),
                _ => Outcome::stuck("unbound variable"),
            };
        }
        let mut kids = Vec::new();
        // `if` is the one constructor that doesn't evaluate all its children.
        let strict = if t.con == IF { 1 } else { t.kids.len() };
        for k in &t.kids[..strict] {
            match self.eval_in(k, env) {
                Value(v) => kids.push(v),
                other => return other.from_inside(),
            }
        }
        match (t.con, &t.atom, kids.as_slice()) {
            (NUM, Atom::Int(n), []) => Value(Num(*n)),
            (STR, Atom::Str(s), []) => Value(Str(s.clone())),
            (TRUE, _, []) => Value(Bool(true)),
            (FALSE, _, []) => Value(Bool(false)),
            (PLUS, _, [Num(a), Num(b)]) => Value(Num(a + b)),
            (PLUS, _, [Str(a), Str(b)]) => Value(Str(format!("{a}{b}"))),
            (MINUS, _, [Num(a), Num(b)]) => Value(Num(a - b)),
            (LT, _, [Num(a), Num(b)]) => Value(Bool(a < b)),
            (EQ, _, [a, b]) => Value(Bool(a == b)),
            (EQ_STRICT, _, [a, b]) if std::mem::discriminant(a) == std::mem::discriminant(b) => {
                Value(Bool(a == b))
            }
            (TYPEOF, _, [v]) => Value(Str(match v {
                Num(_) => "number",
                Str(_) => "string",
                Bool(_) => "boolean",
            }
            .into())),
            (LENGTH, _, [Str(s)]) => Value(Num(s.chars().count() as i64)),
            (IF, _, [Bool(true)]) => self.eval_in(&t.kids[1], env).from_inside(),
            (IF, _, [Bool(false)]) => self.eval_in(&t.kids[2], env).from_inside(),
            _ => Outcome::stuck(format!("{} of {:?}", self.sig[t.con].name, kids)),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(n) => n.to_string(),
            Val::Str(s) => format!("{s:?}"),
            Val::Bool(b) => b.to_string(),
        }
    }
}
