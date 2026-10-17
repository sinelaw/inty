//! Integers and floats: every operation on numbers takes both, but only an
//! integer can say how many times to repeat a string. So integers are
//! accepted wherever floats are, and more: the type system to find has
//! `Int <: Float`, read off the fingerprints' order.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Subtyping {
    sig: Vec<Con>,
}

const INT: usize = 0;
const FLT: usize = 1;
const STR: usize = 2;
const TRUE: usize = 3;
const PLUS: usize = 4;
const FLOOR: usize = 5;
const LT: usize = 6;
const REPEAT: usize = 7;
const LEN: usize = 8;
const IF: usize = 9;
const VAR: usize = 10;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Int(i64),
    /// A float, in halves (so it can be hashed): `Flt(3)` is 1.5.
    Flt(i64),
    Str(String),
    Bool(bool),
}

impl Val {
    fn halves(&self) -> Option<i64> {
        match self {
            Val::Int(n) => Some(2 * n),
            Val::Flt(h) => Some(*h),
            _ => None,
        }
    }
}

impl Default for Subtyping {
    fn default() -> Self {
        Subtyping {
            sig: vec![
                Con::literal("int", vec![Atom::Int(0), Atom::Int(1)]),
                Con::literal("float", vec![Atom::Int(1), Atom::Int(3)]),
                Con::literal("str", vec![Atom::Str(String::new()), Atom::Str("a".into())]),
                Con::op("true", 0),
                Con::op("+", 2),
                Con::op("floor", 1),
                Con::op("<", 2),
                Con::op("repeat", 2),
                Con::op("len", 1),
                Con::op("if", 3),
                Con::var(),
            ],
        }
    }
}

impl Language for Subtyping {
    type Value = Val;

    fn name(&self) -> &str {
        "subtyping (integers are floats, and more)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        use Outcome::Value;
        let kid = |i: usize| self.eval_in(&t.kids[i], env).from_inside();
        macro_rules! value {
            ($e:expr) => {
                match $e {
                    Value(v) => v,
                    other => return other,
                }
            };
        }
        match (t.con, &t.atom) {
            (INT, Atom::Int(n)) => Value(Val::Int(*n)),
            (FLT, Atom::Int(h)) => Value(Val::Flt(*h)),
            (STR, Atom::Str(s)) => Value(Val::Str(s.clone())),
            (TRUE, _) => Value(Val::Bool(true)),
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (PLUS, _) => match (value!(kid(0)), value!(kid(1))) {
                (Val::Int(a), Val::Int(b)) => Value(Val::Int(a.wrapping_add(b))),
                (a, b) => match (a.halves(), b.halves()) {
                    (Some(x), Some(y)) => Value(Val::Flt(x.wrapping_add(y))),
                    _ => Outcome::stuck("not numbers"),
                },
            },
            (FLOOR, _) => match value!(kid(0)).halves() {
                Some(h) => Value(Val::Int(h.div_euclid(2))),
                None => Outcome::stuck("not a number"),
            },
            (LT, _) => match (value!(kid(0)).halves(), value!(kid(1)).halves()) {
                (Some(x), Some(y)) => Value(Val::Bool(x < y)),
                _ => Outcome::stuck("not numbers"),
            },
            (REPEAT, _) => match (value!(kid(0)), value!(kid(1))) {
                (Val::Str(s), Val::Int(n)) => Value(Val::Str(s.repeat(n.clamp(0, 8) as usize))),
                _ => Outcome::stuck("repeat takes a string and an integer"),
            },
            (LEN, _) => match value!(kid(0)) {
                Val::Str(s) => Value(Val::Int(s.len() as i64)),
                _ => Outcome::stuck("not a string"),
            },
            (IF, _) => match value!(kid(0)) {
                Val::Bool(true) => kid(1),
                Val::Bool(false) => kid(2),
                _ => Outcome::stuck("not a boolean"),
            },
            _ => unreachable!(),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Int(n) => n.to_string(),
            Val::Flt(h) => format!("{}", *h as f64 / 2.0),
            Val::Str(s) => format!("{s:?}"),
            Val::Bool(b) => b.to_string(),
        }
    }
}
