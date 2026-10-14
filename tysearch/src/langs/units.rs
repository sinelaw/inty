//! Units of measure: quantities in metres and seconds, which add only to
//! their own unit and multiply into new ones (`m * s`, `m / s`). A type
//! system for them needs arithmetic on types: `* : (U, V) -> U·V`. The
//! rule format has none, so this measures what the search makes of it.
//! Powers are kept to -1, 0 and 1 (past them, a fault), so there are nine
//! units.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Units {
    sig: Vec<Con>,
}

const M: usize = 0;
const S: usize = 1;
const ONE: usize = 2;
const PLUS: usize = 3;
const TIMES: usize = 4;
const DIV: usize = 5;
const LT: usize = 6;
const IF: usize = 7;
const VAR: usize = 8;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    /// A quantity, by the powers of metres and seconds in its unit.
    Q(i8, i8),
    Bool(bool),
}

impl Default for Units {
    fn default() -> Self {
        Units {
            sig: vec![
                Con::op("m", 0),
                Con::op("s", 0),
                Con::op("one", 0),
                Con::op("+", 2),
                Con::op("*", 2),
                Con::op("/", 2),
                Con::op("<", 2),
                Con::op("if", 3),
                Con::var(),
            ],
        }
    }
}

impl Language for Units {
    type Value = Val;

    fn name(&self) -> &str {
        "units (quantities in metres and seconds)"
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
        match (t.con, kids.as_slice()) {
            (M, []) => Value(Q(1, 0)),
            (S, []) => Value(Q(0, 1)),
            (ONE, []) => Value(Q(0, 0)),
            (PLUS, [Q(a, b), Q(c, d)]) if (a, b) == (c, d) => Value(Q(*a, *b)),
            // Powers past one overflow: allowed, as a fault, so that the
            // units stay nine (1, m, s, m·s, m/s, …).
            (TIMES | DIV, [Q(a, b), Q(c, d)]) => {
                let sign = if t.con == TIMES { 1 } else { -1 };
                let (x, y) = (a + sign * c, b + sign * d);
                if x.abs() > 1 || y.abs() > 1 {
                    Fault("unit overflow".into())
                } else {
                    Value(Q(x, y))
                }
            }
            (LT, [Q(a, b), Q(c, d)]) if (a, b) == (c, d) => Value(Bool(true)),
            (IF, [Bool(true)]) => self.eval_in(&t.kids[1], env).from_inside(),
            (IF, [Bool(false)]) => self.eval_in(&t.kids[2], env).from_inside(),
            _ => Outcome::stuck(format!("{} of {:?}", self.sig[t.con].name, kids)),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Q(0, 0) => "1".into(),
            Val::Q(a, b) => {
                let mut parts = Vec::new();
                for (p, u) in [(a, "m"), (b, "s")] {
                    match p {
                        0 => {}
                        1 => parts.push(u.to_string()),
                        p => parts.push(format!("{u}^{p}")),
                    }
                }
                format!("1 {}", parts.join("·"))
            }
            Val::Bool(b) => b.to_string(),
        }
    }
}
