//! An effect: `ask` gives the value of the innermost enclosing `with`, and
//! gets stuck outside any. Its type is not its own, nor its children's, but
//! the context's: a type system for it carries the handler's type down the
//! program, as inty's carries a function's return type. The search finds
//! that for `return` (exit types); this asks whether it can for anything
//! like it.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Effects {
    sig: Vec<Con>,
}

const NUM: usize = 0;
const TRUE: usize = 1;
const PLUS: usize = 2;
const NOT: usize = 3;
const IF: usize = 4;
const ASK: usize = 5;
const WITH: usize = 6;
const VAR: usize = 7;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Num(i64),
    Bool(bool),
}

impl Default for Effects {
    fn default() -> Self {
        Effects {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::op("true", 0),
                Con::op("+", 2),
                Con::op("not", 1),
                Con::op("if", 3),
                Con::op("ask", 0),
                Con::op("with", 2),
                Con::var(),
            ],
        }
    }
}

impl Effects {
    fn ev(&self, t: &Term, env: &[Val], handler: Option<&Val>) -> Outcome<Val> {
        use Outcome::Value;
        let kid = |i: usize, h: Option<&Val>| self.ev(&t.kids[i], env, h).from_inside();
        macro_rules! value {
            ($e:expr) => {
                match $e {
                    Value(v) => v,
                    other => return other,
                }
            };
        }
        match (t.con, &t.atom) {
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (NUM, Atom::Int(n)) => Value(Val::Num(*n)),
            (TRUE, _) => Value(Val::Bool(true)),
            (PLUS, _) => match (value!(kid(0, handler)), value!(kid(1, handler))) {
                (Val::Num(a), Val::Num(b)) => Value(Val::Num(a.wrapping_add(b))),
                _ => Outcome::stuck("not numbers"),
            },
            (NOT, _) => match value!(kid(0, handler)) {
                Val::Bool(b) => Value(Val::Bool(!b)),
                _ => Outcome::stuck("not a boolean"),
            },
            (IF, _) => match value!(kid(0, handler)) {
                Val::Bool(true) => kid(1, handler),
                Val::Bool(false) => kid(2, handler),
                _ => Outcome::stuck("not a boolean"),
            },
            (ASK, _) => match handler {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("ask with no handler"),
            },
            (WITH, _) => {
                let v = value!(kid(0, handler));
                kid(1, Some(&v))
            }
            _ => unreachable!(),
        }
    }
}

impl Language for Effects {
    type Value = Val;

    fn name(&self) -> &str {
        "effects (ask, handled by with)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        self.ev(t, env, None)
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(n) => n.to_string(),
            Val::Bool(b) => b.to_string(),
        }
    }
}
