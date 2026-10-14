//! Information flow: numbers are public or secret, arithmetic on a secret
//! gives a secret, and `print` gets stuck on a secret (a leak), so the
//! explicit flows are safety. The implicit ones (`if secret < 1 then print
//! 0 else print 1`) run fine: the semantics can't see them, so no type
//! system found from it can either. Noninterference is about two runs at
//! once, not one.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Secrets {
    sig: Vec<Con>,
}

const NUM: usize = 0;
const SECRET: usize = 1;
const PLUS: usize = 2;
const LT: usize = 3;
const IF: usize = 4;
const PRINT: usize = 5;
const DECLASSIFY: usize = 6;
const VAR: usize = 7;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    /// A number, and whether it is secret.
    Num(i64, bool),
    Bool(bool),
}

impl Default for Secrets {
    fn default() -> Self {
        Secrets {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::op("secret", 0),
                Con::op("+", 2),
                Con::op("<", 2),
                Con::op("if", 3),
                Con::op("print", 1),
                Con::op("declassify", 1),
                Con::var(),
            ],
        }
    }
}

impl Language for Secrets {
    type Value = Val;

    fn name(&self) -> &str {
        "secrets (information flow: print gets stuck on a secret)"
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
        let strict = if t.con == IF { 1 } else { t.kids.len() };
        let mut kids = Vec::new();
        for k in &t.kids[..strict] {
            match self.eval_in(k, env) {
                Value(v) => kids.push(v),
                other => return other.from_inside(),
            }
        }
        match (t.con, &t.atom, kids.as_slice()) {
            (NUM, Atom::Int(n), []) => Value(Num(*n, false)),
            (SECRET, _, []) => Value(Num(7, true)),
            (PLUS, _, [Num(a, x), Num(b, y)]) => Value(Num(a.wrapping_add(*b), *x || *y)),
            // Comparing a secret gives a public boolean: the implicit flow
            // the semantics doesn't track.
            (LT, _, [Num(a, _), Num(b, _)]) => Value(Bool(a < b)),
            (IF, _, [Bool(true)]) => self.eval_in(&t.kids[1], env).from_inside(),
            (IF, _, [Bool(false)]) => self.eval_in(&t.kids[2], env).from_inside(),
            (PRINT, _, [Num(n, false)]) => Value(Num(*n, false)),
            (PRINT, _, [Num(_, true)]) => Outcome::stuck("leak: print of a secret"),
            (DECLASSIFY, _, [Num(n, _)]) => Value(Num(*n, false)),
            _ => Outcome::stuck(format!("{} of {:?}", self.sig[t.con].name, kids)),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(n, false) => n.to_string(),
            Val::Num(n, true) => format!("secret {n}"),
            Val::Bool(b) => b.to_string(),
        }
    }
}
