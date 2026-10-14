//! A control: a language where nothing gets stuck. Every operator takes
//! every value, coercing as it must, so one type is all a type system can
//! say, and the search should find no distinctions.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Unityped {
    sig: Vec<Con>,
}

const NUM: usize = 0;
const STR: usize = 1;
const PLUS: usize = 2;
const NUMBER: usize = 3;
const IF: usize = 4;
const EQ: usize = 5;
const VAR: usize = 6;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Num(i64),
    Str(String),
}

impl Val {
    fn text(&self) -> String {
        match self {
            Val::Num(n) => n.to_string(),
            Val::Str(s) => s.clone(),
        }
    }

    fn number(&self) -> i64 {
        match self {
            Val::Num(n) => *n,
            Val::Str(s) => s.parse().unwrap_or(0),
        }
    }

    fn truthy(&self) -> bool {
        self.number() != 0
    }
}

impl Default for Unityped {
    fn default() -> Self {
        Unityped {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::literal("str", vec![Atom::Str(String::new()), Atom::Str("a".into())]),
                Con::op("+", 2),
                Con::op("number", 1),
                Con::op("if", 3),
                Con::op("==", 2),
                Con::var(),
            ],
        }
    }
}

impl Language for Unityped {
    type Value = Val;

    fn name(&self) -> &str {
        "unityped (nothing gets stuck)"
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
            (NUM, Atom::Int(n)) => Value(Val::Num(*n)),
            (STR, Atom::Str(s)) => Value(Val::Str(s.clone())),
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (PLUS, _) => match (value!(kid(0)), value!(kid(1))) {
                (Val::Num(a), Val::Num(b)) => Value(Val::Num(a.wrapping_add(b))),
                (a, b) => Value(Val::Str(a.text() + &b.text())),
            },
            (NUMBER, _) => Value(Val::Num(value!(kid(0)).number())),
            (IF, _) => {
                if value!(kid(0)).truthy() {
                    kid(1)
                } else {
                    kid(2)
                }
            }
            (EQ, _) => {
                let (a, b) = (value!(kid(0)), value!(kid(1)));
                Value(Val::Num((a.text() == b.text()) as i64))
            }
            _ => unreachable!(),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(n) => n.to_string(),
            Val::Str(s) => format!("{s:?}"),
        }
    }
}
