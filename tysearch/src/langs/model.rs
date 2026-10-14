//! The model under test: a growing copy of the semantics of inty's Lean
//! model (`lean/Inty/Semantics.lean`), one feature at a time. Each
//! iteration (ITERATIONS.md) adds features here, then improves the search
//! until it finds their typing rules.
//!
//! So far (iteration 1): the literals, `!`, `typeof` and unary `-`, the
//! binary operators `+` (numbers or strings), `-`, `*`, `<` (numbers) and
//! `===` (anything), the conditional (read by truthiness, so any test),
//! `const` bindings, and functions of one and two parameters that can call
//! themselves, with calls that ignore extra arguments and get stuck on
//! missing ones, as the model's do.
//!
//! Variables are de Bruijn indices. In a function's body `var(i)` is
//! parameter `i` for `i` below the arity, and `var(arity)` is the function
//! itself, as in the model.

use crate::lang::{Atom, Con, Language, Outcome, Term};
use std::cell::Cell;
use std::rc::Rc;

pub struct Model {
    sig: Vec<Con>,
    /// Calls a run may make before it times out.
    pub fuel: usize,
}

const NUM: usize = 0;
const STR: usize = 1;
const TRUE: usize = 2;
const FALSE: usize = 3;
const UNDEFINED: usize = 4;
const NULL: usize = 5;
const NOT: usize = 6;
const TYPEOF: usize = 7;
const NEG: usize = 8;
const PLUS: usize = 9;
const MINUS: usize = 10;
const TIMES: usize = 11;
const LT: usize = 12;
const EQ: usize = 13;
const COND: usize = 14;
const LET: usize = 15;
const FUNC1: usize = 16;
const FUNC2: usize = 17;
const APP1: usize = 18;
const APP2: usize = 19;
const VAR: usize = 20;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Closure {
    pub arity: usize,
    pub body: Term,
    pub env: Vec<Val>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    /// A double, by its bits (so values can be hashed).
    Num(u64),
    Str(String),
    Bool(bool),
    Undefined,
    Null,
    Clo(Rc<Closure>),
}

fn num(f: f64) -> Val {
    Val::Num(f.to_bits())
}

impl Val {
    /// JavaScript truthiness, as `Value.truthy` in the model.
    fn truthy(&self) -> bool {
        match self {
            Val::Num(b) => {
                let n = f64::from_bits(*b);
                n != 0.0 && !n.is_nan()
            }
            Val::Str(s) => !s.is_empty(),
            Val::Bool(b) => *b,
            Val::Undefined | Val::Null => false,
            Val::Clo(_) => true,
        }
    }

    fn strict_eq(&self, other: &Val) -> bool {
        match (self, other) {
            (Val::Num(a), Val::Num(b)) => f64::from_bits(*a) == f64::from_bits(*b),
            (Val::Clo(a), Val::Clo(b)) => Rc::ptr_eq(a, b),
            (a, b) => a == b,
        }
    }
}

impl Default for Model {
    fn default() -> Self {
        Model {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::literal("str", vec![Atom::Str(String::new()), Atom::Str("a".into())]),
                Con::op("true", 0),
                Con::op("false", 0),
                Con::op("undefined", 0),
                Con::op("null", 0),
                Con::op("!", 1),
                Con::op("typeof", 1),
                Con::op("neg", 1),
                Con::op("+", 2),
                Con::op("-", 2),
                Con::op("*", 2),
                Con::op("<", 2),
                Con::op("===", 2),
                Con::op("cond", 3),
                Con::binder("const", vec![0, 1]),
                Con::binder("func1", vec![2]),
                Con::binder("func2", vec![3]),
                Con::op("app1", 2),
                Con::op("app2", 3),
                Con::var(),
            ],
            fuel: 64,
        }
    }
}

impl Model {
    fn ev(&self, t: &Term, env: &[Val], fuel: &Cell<usize>) -> Outcome<Val> {
        use Outcome::Value;
        let kid = |i: usize, env: &[Val]| self.ev(&t.kids[i], env, fuel).from_inside();
        macro_rules! value {
            ($e:expr) => {
                match $e {
                    Value(v) => v,
                    other => return other,
                }
            };
        }
        match t.con {
            NUM => match t.atom {
                Atom::Int(n) => Value(num(n as f64)),
                _ => unreachable!(),
            },
            STR => match &t.atom {
                Atom::Str(s) => Value(Val::Str(s.clone())),
                _ => unreachable!(),
            },
            TRUE => Value(Val::Bool(true)),
            FALSE => Value(Val::Bool(false)),
            UNDEFINED => Value(Val::Undefined),
            NULL => Value(Val::Null),
            VAR => match t.atom {
                Atom::Int(i) if (i as usize) < env.len() => Value(env[i as usize].clone()),
                _ => Outcome::stuck("undefinedVariable"),
            },
            NOT => Value(Val::Bool(!value!(kid(0, env)).truthy())),
            TYPEOF => Value(Val::Str(
                match value!(kid(0, env)) {
                    Val::Num(_) => "number",
                    Val::Str(_) => "string",
                    Val::Bool(_) => "boolean",
                    Val::Undefined => "undefined",
                    Val::Null => "object",
                    Val::Clo(_) => "function",
                }
                .into(),
            )),
            NEG => match value!(kid(0, env)) {
                Val::Num(b) => Value(num(-f64::from_bits(b))),
                _ => Outcome::stuck("typeMismatch"),
            },
            PLUS | MINUS | TIMES | LT | EQ => {
                let a = value!(kid(0, env));
                let b = value!(kid(1, env));
                match (t.con, &a, &b) {
                    (EQ, a, b) => Value(Val::Bool(a.strict_eq(b))),
                    (PLUS, Val::Str(x), Val::Str(y)) => Value(Val::Str(format!("{x}{y}"))),
                    (_, Val::Num(x), Val::Num(y)) => {
                        let (x, y) = (f64::from_bits(*x), f64::from_bits(*y));
                        Value(match t.con {
                            PLUS => num(x + y),
                            MINUS => num(x - y),
                            TIMES => num(x * y),
                            _ => Val::Bool(x < y),
                        })
                    }
                    _ => Outcome::stuck("typeMismatch"),
                }
            }
            COND => {
                if value!(kid(0, env)).truthy() {
                    kid(1, env)
                } else {
                    kid(2, env)
                }
            }
            LET => {
                let v = value!(kid(0, env));
                let mut inner = vec![v];
                inner.extend_from_slice(env);
                kid(1, &inner)
            }
            FUNC1 | FUNC2 => Value(Val::Clo(Rc::new(Closure {
                arity: if t.con == FUNC1 { 1 } else { 2 },
                body: t.kids[0].clone(),
                env: env.to_vec(),
            }))),
            APP1 | APP2 => {
                let f = value!(kid(0, env));
                let mut args = Vec::new();
                for i in 1..t.kids.len() {
                    args.push(value!(kid(i, env)));
                }
                let Val::Clo(c) = &f else {
                    return Outcome::stuck("notCallable");
                };
                if args.len() < c.arity {
                    return Outcome::stuck("arityMismatch");
                }
                if fuel.get() == 0 {
                    return Outcome::Timeout;
                }
                fuel.set(fuel.get() - 1);
                // Extra arguments are ignored, as in JavaScript.
                let mut inner: Vec<Val> = args[..c.arity].to_vec();
                inner.push(f.clone());
                inner.extend_from_slice(&c.env);
                self.ev(&c.body, &inner, fuel).from_inside()
            }
            _ => unreachable!(),
        }
    }
}

impl Language for Model {
    type Value = Val;

    fn name(&self) -> &str {
        "model (inty's Lean model, iteration 1: functions and const)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        self.ev(t, env, &Cell::new(self.fuel))
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(b) => f64::from_bits(*b).to_string(),
            Val::Str(s) => format!("{s:?}"),
            Val::Bool(b) => b.to_string(),
            Val::Undefined => "undefined".into(),
            Val::Null => "null".into(),
            Val::Clo(c) => format!("fn{}({})", c.arity, self.show_term(&c.body)),
        }
    }
}
