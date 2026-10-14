//! A first-order slice of the operators of inty's Lean model
//! (`lean/Inty/Syntax.lean`): numbers, strings and booleans, `+` on two
//! numbers or two strings (inty's `Plus` class), `-` and `<` on numbers,
//! `===` and `typeof` on anything, string `.length`, and the conditional.
//!
//! Unlike JavaScript, and like the model, `1 + "a"` and `1 < "a"` are stuck.

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

    fn eval(&self, t: &Term) -> Outcome<Val> {
        use Outcome::*;
        use Val::*;
        let mut kids = Vec::new();
        // `if` is the one constructor that doesn't evaluate all its children.
        let strict = if t.con == IF { 1 } else { t.kids.len() };
        for k in &t.kids[..strict] {
            match self.eval(k) {
                Value(v) => kids.push(v),
                other => return other,
            }
        }
        let stuck = || Stuck(format!("{} of {:?}", self.sig[t.con].name, kids));
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
            (TYPEOF, _, [v]) => Value(Str(match v {
                Num(_) => "number",
                Str(_) => "string",
                Bool(_) => "boolean",
            }
            .into())),
            (LENGTH, _, [Str(s)]) => Value(Num(s.chars().count() as i64)),
            (IF, _, [Bool(true)]) => self.eval(&t.kids[1]),
            (IF, _, [Bool(false)]) => self.eval(&t.kids[2]),
            _ => stuck(),
        }
    }

    fn quote(&self, v: &Val) -> Term {
        match v {
            Val::Num(n) => Term::leaf(NUM, Atom::Int(*n)),
            Val::Str(s) => Term::leaf(STR, Atom::Str(s.clone())),
            Val::Bool(true) => Term::leaf(TRUE, Atom::None),
            Val::Bool(false) => Term::leaf(FALSE, Atom::None),
        }
    }
}
