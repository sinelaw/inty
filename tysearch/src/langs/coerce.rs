//! JavaScript's coercions, which inty's model leaves out: `+` concatenates
//! when either side is a string and adds otherwise, reading `true` as 1 and
//! `null` as 0; `-` reads both sides as numbers. Only `.length` (strings)
//! and `.toFixed()` (numbers) are particular about what they take. The
//! type system to find is not inty's: `+` takes anything.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Coerce {
    sig: Vec<Con>,
}

const NUM: usize = 0;
const STR: usize = 1;
const TRUE: usize = 2;
const NULL: usize = 3;
const PLUS: usize = 4;
const MINUS: usize = 5;
const LENGTH: usize = 6;
const TOFIXED: usize = 7;
const IF: usize = 8;
const VAR: usize = 9;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Num(i64),
    Str(String),
    Bool(bool),
    Null,
}

impl Val {
    fn text(&self) -> String {
        match self {
            Val::Num(n) => n.to_string(),
            Val::Str(s) => s.clone(),
            Val::Bool(b) => b.to_string(),
            Val::Null => "null".into(),
        }
    }

    fn number(&self) -> i64 {
        match self {
            Val::Num(n) => *n,
            Val::Str(s) => s.parse().unwrap_or(0),
            Val::Bool(b) => *b as i64,
            Val::Null => 0,
        }
    }

    fn truthy(&self) -> bool {
        match self {
            Val::Num(n) => *n != 0,
            Val::Str(s) => !s.is_empty(),
            Val::Bool(b) => *b,
            Val::Null => false,
        }
    }
}

impl Default for Coerce {
    fn default() -> Self {
        Coerce {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::literal("str", vec![Atom::Str(String::new()), Atom::Str("a".into())]),
                Con::op("true", 0),
                Con::op("null", 0),
                Con::op("+", 2),
                Con::op("-", 2),
                Con::op("length", 1),
                Con::op("toFixed", 1),
                Con::op("if", 3),
                Con::var(),
            ],
        }
    }
}

impl Language for Coerce {
    type Value = Val;

    fn name(&self) -> &str {
        "coerce (JavaScript's + and -)"
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
            (TRUE, _) => Value(Val::Bool(true)),
            (NULL, _) => Value(Val::Null),
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (PLUS, _) => match (value!(kid(0)), value!(kid(1))) {
                (a @ Val::Str(_), b) | (a, b @ Val::Str(_)) => {
                    Value(Val::Str(a.text() + &b.text()))
                }
                (a, b) => Value(Val::Num(a.number().wrapping_add(b.number()))),
            },
            (MINUS, _) => {
                let (a, b) = (value!(kid(0)), value!(kid(1)));
                Value(Val::Num(a.number().wrapping_sub(b.number())))
            }
            (LENGTH, _) => match value!(kid(0)) {
                Val::Str(s) => Value(Val::Num(s.len() as i64)),
                _ => Outcome::stuck("not a string"),
            },
            (TOFIXED, _) => match value!(kid(0)) {
                Val::Num(n) => Value(Val::Str(format!("{n}.00"))),
                _ => Outcome::stuck("not a number"),
            },
            (IF, _) => {
                if value!(kid(0)).truthy() {
                    kid(1)
                } else {
                    kid(2)
                }
            }
            _ => unreachable!(),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Str(s) => format!("{s:?}"),
            v => v.text(),
        }
    }
}
