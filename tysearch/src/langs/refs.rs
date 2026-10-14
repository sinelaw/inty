//! ML's references: `ref e` makes a cell, `get r` reads it, `set r v`
//! stores `v` and gives it, alongside numbers, booleans, `let` and
//! functions. Two things to find: that a cell's type is invariant (`set`
//! must store what the cell holds), and Wright's value restriction: `let`
//! may generalise `(x) => x` but not `ref((x) => x)`, or `r` could hold a
//! number function and be read as a string function.

use crate::lang::{Atom, Con, Language, Outcome, Term};
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub struct Refs {
    sig: Vec<Con>,
    pub fuel: usize,
}

const NUM: usize = 0;
const TRUE: usize = 1;
const FALSE: usize = 2;
const PLUS: usize = 3;
const NOT: usize = 4;
const IF: usize = 5;
const LET: usize = 6;
const FUNC: usize = 7;
const APP: usize = 8;
const REF: usize = 9;
const GET: usize = 10;
const SET: usize = 11;
const SEQ: usize = 12;
const VAR: usize = 13;

/// A reference cell. Two are equal only if they are the same cell.
#[derive(Clone, Debug)]
pub struct Cell_(Rc<RefCell<Val>>);

impl PartialEq for Cell_ {
    fn eq(&self, other: &Cell_) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Cell_ {}

impl Hash for Cell_ {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(h)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    Num(i64),
    Bool(bool),
    Clo(Rc<(Term, Vec<Val>)>),
    Ref(Cell_),
}

impl Val {
    /// A copy with cells of its own, to a bounded depth.
    fn isolate(&self, depth: usize) -> Val {
        match self {
            Val::Ref(c) if depth > 0 => Val::Ref(Cell_(Rc::new(RefCell::new(
                c.0.borrow().isolate(depth - 1),
            )))),
            Val::Clo(c) if depth > 0 => Val::Clo(Rc::new((
                c.0.clone(),
                c.1.iter().map(|v| v.isolate(depth - 1)).collect(),
            ))),
            v => v.clone(),
        }
    }

    /// Structural, cells by contents to a bounded depth.
    fn same(&self, other: &Val, depth: usize) -> bool {
        match (self, other) {
            (Val::Ref(a), Val::Ref(b)) => {
                a == b || (depth > 0 && a.0.borrow().same(&b.0.borrow(), depth - 1))
            }
            (Val::Clo(a), Val::Clo(b)) => {
                a.0 == b.0
                    && a.1.len() == b.1.len()
                    && (depth == 0 || a.1.iter().zip(&b.1).all(|(x, y)| x.same(y, depth - 1)))
            }
            (a, b) => a == b,
        }
    }
}

impl Default for Refs {
    fn default() -> Self {
        Refs {
            sig: vec![
                Con::literal("num", vec![Atom::Int(0), Atom::Int(1)]),
                Con::op("true", 0),
                Con::op("false", 0),
                Con::op("+", 2),
                Con::op("not", 1),
                Con::op("if", 3),
                Con::binder("let", vec![0, 1]),
                Con::binder("func", vec![2]),
                Con::op("app", 2),
                Con::op("ref", 1),
                Con::op("get", 1),
                Con::op("set", 2),
                Con::op("seq", 2),
                Con::var(),
            ],
            fuel: 64,
        }
    }
}

impl Refs {
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
        match (t.con, &t.atom) {
            (NUM, Atom::Int(n)) => Value(Val::Num(*n)),
            (TRUE, _) => Value(Val::Bool(true)),
            (FALSE, _) => Value(Val::Bool(false)),
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (PLUS, _) => match (value!(kid(0, env)), value!(kid(1, env))) {
                (Val::Num(a), Val::Num(b)) => Value(Val::Num(a.wrapping_add(b))),
                _ => Outcome::stuck("not numbers"),
            },
            (NOT, _) => match value!(kid(0, env)) {
                Val::Bool(b) => Value(Val::Bool(!b)),
                _ => Outcome::stuck("not a boolean"),
            },
            (IF, _) => match value!(kid(0, env)) {
                Val::Bool(true) => kid(1, env),
                Val::Bool(false) => kid(2, env),
                _ => Outcome::stuck("not a boolean"),
            },
            (LET, _) => {
                let v = value!(kid(0, env));
                let mut inner = vec![v];
                inner.extend_from_slice(env);
                kid(1, &inner)
            }
            (FUNC, _) => Value(Val::Clo(Rc::new((t.kids[0].clone(), env.to_vec())))),
            (APP, _) => {
                let f = value!(kid(0, env));
                let a = value!(kid(1, env));
                let Val::Clo(c) = &f else {
                    return Outcome::stuck("not a function");
                };
                if fuel.get() == 0 {
                    return Outcome::Timeout;
                }
                fuel.set(fuel.get() - 1);
                let mut inner = vec![a, f.clone()];
                inner.extend_from_slice(&c.1);
                self.ev(&c.0, &inner, fuel).from_inside()
            }
            (REF, _) => Value(Val::Ref(Cell_(Rc::new(RefCell::new(value!(kid(0, env))))))),
            (GET, _) => match value!(kid(0, env)) {
                Val::Ref(c) => Value(c.0.borrow().clone()),
                _ => Outcome::stuck("not a reference"),
            },
            (SET, _) => {
                let r = value!(kid(0, env));
                let v = value!(kid(1, env));
                match r {
                    Val::Ref(c) => {
                        *c.0.borrow_mut() = v.clone();
                        Value(v)
                    }
                    _ => Outcome::stuck("not a reference"),
                }
            }
            (SEQ, _) => {
                value!(kid(0, env));
                kid(1, env)
            }
            _ => unreachable!(),
        }
    }
}

impl Language for Refs {
    type Value = Val;

    fn name(&self) -> &str {
        "refs (ML's references, and let-polymorphism)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        self.ev(t, env, &Cell::new(self.fuel))
    }

    fn same(&self, a: &Val, b: &Val) -> bool {
        a.same(b, 3)
    }

    fn isolate(&self, v: &Val) -> Val {
        v.isolate(6)
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(n) => n.to_string(),
            Val::Bool(b) => b.to_string(),
            Val::Clo(c) => format!("fn({})", self.show_term(&c.0)),
            Val::Ref(c) => format!("ref {}", self.show_value(&c.0.borrow())),
        }
    }
}
