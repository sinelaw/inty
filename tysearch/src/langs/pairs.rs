//! Products: `pair(a, b)` taken apart by `fst` and `snd`, with numbers,
//! booleans and a strict conditional. A pair's sort has two eliminators,
//! so its refinement needs both: the type to find is `a × b`.

use crate::lang::{Atom, Con, Language, Outcome, Term};
use std::rc::Rc;

pub struct Pairs {
    sig: Vec<Con>,
}

const NUM: usize = 0;
const TRUE: usize = 1;
const FALSE: usize = 2;
const PAIR: usize = 3;
const FST: usize = 4;
const SND: usize = 5;
const PLUS: usize = 6;
const NOT: usize = 7;
const IF: usize = 8;
const VAR: usize = 9;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Num(i64),
    Bool(bool),
    Pair(Rc<(Val, Val)>),
}

impl Default for Pairs {
    fn default() -> Self {
        Pairs {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::op("true", 0),
                Con::op("false", 0),
                Con::op("pair", 2),
                Con::op("fst", 1),
                Con::op("snd", 1),
                Con::op("+", 2),
                Con::op("not", 1),
                Con::op("if", 3),
                Con::var(),
            ],
        }
    }
}

impl Language for Pairs {
    type Value = Val;

    fn name(&self) -> &str {
        "pairs (products with two eliminators)"
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
            (TRUE, _) => Value(Val::Bool(true)),
            (FALSE, _) => Value(Val::Bool(false)),
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (PAIR, _) => {
                let a = value!(kid(0));
                let b = value!(kid(1));
                Value(Val::Pair(Rc::new((a, b))))
            }
            (FST, _) | (SND, _) => match value!(kid(0)) {
                Val::Pair(p) => Value(if t.con == FST {
                    p.0.clone()
                } else {
                    p.1.clone()
                }),
                _ => Outcome::stuck("not a pair"),
            },
            (PLUS, _) => match (value!(kid(0)), value!(kid(1))) {
                (Val::Num(a), Val::Num(b)) => Value(Val::Num(a.wrapping_add(b))),
                _ => Outcome::stuck("not numbers"),
            },
            (NOT, _) => match value!(kid(0)) {
                Val::Bool(b) => Value(Val::Bool(!b)),
                _ => Outcome::stuck("not a boolean"),
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
            Val::Num(n) => n.to_string(),
            Val::Bool(b) => b.to_string(),
            Val::Pair(p) => format!("({}, {})", self.show_value(&p.0), self.show_value(&p.1)),
        }
    }
}
