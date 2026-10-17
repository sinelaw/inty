//! The untyped arithmetic expressions of Pierce's *Types and Programming
//! Languages*, chapter 3: booleans, numerals and conditionals. Chapter 8
//! types them with `Bool` and `Nat`; the search should find the same.

use crate::lang::{Con, Language, Outcome, Term};

pub struct Arith {
    sig: Vec<Con>,
}

const TRUE: usize = 0;
const FALSE: usize = 1;
const ZERO: usize = 2;
const SUCC: usize = 3;
const PRED: usize = 4;
const ISZERO: usize = 5;
const IF: usize = 6;
const VAR: usize = 7;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Bool(bool),
    Nat(u64),
}

impl Default for Arith {
    fn default() -> Self {
        Arith {
            sig: vec![
                Con::op("true", 0),
                Con::op("false", 0),
                Con::op("zero", 0),
                Con::op("succ", 1),
                Con::op("pred", 1),
                Con::op("iszero", 1),
                Con::op("if", 3),
                Con::var(),
            ],
        }
    }
}

impl Language for Arith {
    type Value = Val;

    fn name(&self) -> &str {
        "arith (TAPL ch. 3)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    /// Big-step, after TAPL's small-step rules: `pred zero` is `zero`, and
    /// a numeral in a boolean position (or the converse) is stuck.
    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        use Outcome::*;
        let ev = |i: usize| self.eval_in(&t.kids[i], env).from_inside();
        match t.con {
            TRUE => Value(Val::Bool(true)),
            FALSE => Value(Val::Bool(false)),
            ZERO => Value(Val::Nat(0)),
            SUCC | PRED | ISZERO => match ev(0) {
                Value(Val::Nat(n)) => Value(match t.con {
                    SUCC => Val::Nat(n + 1),
                    PRED => Val::Nat(n.saturating_sub(1)),
                    _ => Val::Bool(n == 0),
                }),
                Value(Val::Bool(_)) => {
                    Outcome::stuck(format!("{} of a boolean", self.sig[t.con].name))
                }
                other => other,
            },
            IF => match ev(0) {
                Value(Val::Bool(true)) => ev(1),
                Value(Val::Bool(false)) => ev(2),
                Value(Val::Nat(_)) => Outcome::stuck("if on a numeral"),
                other => other,
            },
            VAR => match t.atom {
                crate::lang::Atom::Int(i) if (i as usize) < env.len() => {
                    Value(env[i as usize].clone())
                }
                _ => Outcome::stuck("unbound variable"),
            },
            _ => unreachable!(),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Bool(b) => b.to_string(),
            Val::Nat(n) => n.to_string(),
        }
    }
}
