//! printf: `fmt(s)` makes a formatter wanting one argument per `%` in `s`,
//! `arg(f, x)` gives it one, and `done(f)` the string, stuck if arguments
//! are missing or too many. The type of `fmt(s)` depends on the string's
//! contents, a value, not its type: dependent types, which the rule format
//! has none of.

use crate::lang::{Atom, Con, Language, Outcome, Term};

pub struct Printf {
    sig: Vec<Con>,
}

const STR: usize = 0;
const NUM: usize = 1;
const FMT: usize = 2;
const ARG: usize = 3;
const DONE: usize = 4;
const VAR: usize = 5;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Str(String),
    Num(i64),
    /// A formatter: how many arguments it still wants, and its text.
    Fmt(usize, String),
}

impl Default for Printf {
    fn default() -> Self {
        Printf {
            sig: vec![
                Con::literal(
                    "str",
                    vec![
                        Atom::Str(String::new()),
                        Atom::Str("%".into()),
                        Atom::Str("%%".into()),
                    ],
                ),
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::op("fmt", 1),
                Con::op("arg", 2),
                Con::op("done", 1),
                Con::var(),
            ],
        }
    }
}

impl Language for Printf {
    type Value = Val;

    fn name(&self) -> &str {
        "printf (formatters whose arity is in a string)"
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
        for k in &t.kids {
            match self.eval_in(k, env) {
                Value(v) => kids.push(v),
                other => return other.from_inside(),
            }
        }
        match (t.con, &t.atom, kids.as_slice()) {
            (STR, Atom::Str(s), []) => Value(Str(s.clone())),
            (NUM, Atom::Int(n), []) => Value(Num(*n)),
            (FMT, _, [Str(s)]) => Value(Fmt(s.matches('%').count(), s.clone())),
            (ARG, _, [Fmt(n, s), x]) if *n > 0 && !matches!(x, Fmt(..)) => {
                let shown = match x {
                    Num(k) => k.to_string(),
                    Str(t) => t.clone(),
                    Fmt(..) => unreachable!(),
                };
                Value(Fmt(n - 1, s.replacen('%', &shown, 1)))
            }
            (DONE, _, [Fmt(0, s)]) => Value(Str(s.clone())),
            _ => Outcome::stuck(format!("{} of {:?}", self.sig[t.con].name, kids)),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Str(s) => format!("{s:?}"),
            Val::Num(n) => n.to_string(),
            Val::Fmt(n, s) => format!("fmt[{n} more]({s:?})"),
        }
    }
}
