//! The model under test: a growing copy of the semantics of inty's Lean
//! model (`lean/Inty/Semantics.lean`), one feature at a time. Each
//! iteration (ITERATIONS.md) adds features here, then improves the search
//! until it finds their typing rules.
//!
//! So far: the literals, `!`, `typeof` and unary `-`, the binary operators
//! `+` (numbers or strings), `-`, `*`, `<` (numbers) and `===` (anything),
//! the conditional (read by truthiness, so any test), and functions of one
//! and two parameters that can call themselves, with calls that ignore
//! extra arguments and get stuck on missing ones, as the model's do
//! (iteration 1); and variables in cells, as the model's environment holds
//! them: `let`, assignment `x = e`, which closures see, and `e₁; e₂`
//! (iteration 3); and objects with properties `x` and `y`, read with `.x`,
//! stored with `.x =` (iteration 5).
//!
//! Variables are de Bruijn indices. In a function's body `var(i)` is
//! parameter `i` for `i` below the arity, and `var(arity)` is the function
//! itself, as in the model.

use crate::lang::{Atom, Con, Language, Outcome, Term};
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};
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
const ASSIGN: usize = 21;
const SEQ: usize = 22;
const OBJ_X: usize = 23;
const OBJ_Y: usize = 24;
const OBJ_XY: usize = 25;
const GET_X: usize = 26;
const GET_Y: usize = 27;
const SET_X: usize = 28;
const SET_Y: usize = 29;

/// An object's cell: its properties, in order. Two objects are the same
/// object only if they are the same cell, as `===` sees them.
#[derive(Clone)]
pub struct ObjCell(Rc<RefCell<Vec<(&'static str, Val)>>>);

impl std::fmt::Debug for ObjCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "obj@{:p}", Rc::as_ptr(&self.0))
    }
}

impl PartialEq for ObjCell {
    fn eq(&self, other: &ObjCell) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for ObjCell {}

impl Hash for ObjCell {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(h)
    }
}

/// A variable's cell. Two are equal only if they are the same cell.
#[derive(Clone)]
pub struct Slot(Rc<RefCell<Val>>);

/// Not its contents: a closure stored in a cell it captures is a cycle.
impl std::fmt::Debug for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cell@{:p}", Rc::as_ptr(&self.0))
    }
}

impl Slot {
    fn new(v: Val) -> Slot {
        Slot(Rc::new(RefCell::new(v)))
    }

    fn get(&self) -> Val {
        self.0.borrow().clone()
    }
}

impl PartialEq for Slot {
    fn eq(&self, other: &Slot) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Slot {}

impl Hash for Slot {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(h)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Closure {
    pub arity: usize,
    pub body: Term,
    pub env: Vec<Slot>,
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
    Obj(ObjCell),
}

fn num(f: f64) -> Val {
    Val::Num(f.to_bits())
}

impl Val {
    /// Structural equality, cells compared by their contents to a bounded
    /// depth (an assigned cell can hold a closure over itself).
    fn same(&self, other: &Val, depth: usize) -> bool {
        match (self, other) {
            (Val::Clo(a), Val::Clo(b)) => {
                Rc::ptr_eq(a, b)
                    || (a.arity == b.arity
                        && a.body == b.body
                        && a.env.len() == b.env.len()
                        && (depth == 0
                            || a.env
                                .iter()
                                .zip(&b.env)
                                .all(|(x, y)| x == y || x.get().same(&y.get(), depth - 1))))
            }
            (Val::Obj(a), Val::Obj(b)) => {
                a == b || {
                    let (x, y) = (a.0.borrow(), b.0.borrow());
                    x.len() == y.len()
                        && (depth == 0
                            || x.iter()
                                .zip(y.iter())
                                .all(|((l, v), (m, w))| l == m && v.same(w, depth - 1)))
                }
            }
            (a, b) => a == b,
        }
    }

    /// A copy whose closures have cells of their own, to a bounded depth.
    fn isolate(&self, depth: usize) -> Val {
        match self {
            Val::Clo(c) if depth > 0 => Val::Clo(Rc::new(Closure {
                arity: c.arity,
                body: c.body.clone(),
                env: c
                    .env
                    .iter()
                    .map(|s| Slot::new(s.get().isolate(depth - 1)))
                    .collect(),
            })),
            Val::Obj(o) if depth > 0 => Val::Obj(ObjCell(Rc::new(RefCell::new(
                o.0.borrow()
                    .iter()
                    .map(|(l, v)| (*l, v.isolate(depth - 1)))
                    .collect(),
            )))),
            v => v.clone(),
        }
    }

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
            Val::Clo(_) | Val::Obj(_) => true,
        }
    }

    fn strict_eq(&self, other: &Val) -> bool {
        match (self, other) {
            (Val::Num(a), Val::Num(b)) => f64::from_bits(*a) == f64::from_bits(*b),
            (Val::Clo(a), Val::Clo(b)) => Rc::ptr_eq(a, b),
            (Val::Obj(a), Val::Obj(b)) => a == b,
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
                Con::binder("let", vec![0, 1]),
                Con::binder("func1", vec![2]),
                Con::binder("func2", vec![3]),
                Con::op("app1", 2),
                Con::op("app2", 3),
                Con::var(),
                Con::assign(),
                Con::op("seq", 2),
                Con::op("{x}", 1),
                Con::op("{y}", 1),
                Con::op("{x,y}", 2),
                Con::op(".x", 1),
                Con::op(".y", 1),
                Con::op(".x=", 2),
                Con::op(".y=", 2),
            ],
            fuel: 64,
        }
    }
}

impl Model {
    fn ev(&self, t: &Term, env: &[Slot], fuel: &Cell<usize>) -> Outcome<Val> {
        use Outcome::Value;
        let kid = |i: usize, env: &[Slot]| self.ev(&t.kids[i], env, fuel).from_inside();
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
                Atom::Int(i) if (i as usize) < env.len() => Value(env[i as usize].get()),
                _ => Outcome::stuck("undefinedVariable"),
            },
            ASSIGN => match t.atom {
                Atom::Int(i) if (i as usize) < env.len() => {
                    let v = value!(kid(0, env));
                    *env[i as usize].0.borrow_mut() = v.clone();
                    Value(v)
                }
                _ => Outcome::stuck("undefinedVariable"),
            },
            OBJ_X | OBJ_Y | OBJ_XY => {
                let labels: &[&'static str] = match t.con {
                    OBJ_X => &["x"],
                    OBJ_Y => &["y"],
                    _ => &["x", "y"],
                };
                let mut fields = Vec::new();
                for (i, l) in labels.iter().enumerate() {
                    fields.push((*l, value!(kid(i, env))));
                }
                Value(Val::Obj(ObjCell(Rc::new(RefCell::new(fields)))))
            }
            GET_X | GET_Y | SET_X | SET_Y => {
                let label = if matches!(t.con, GET_X | SET_X) {
                    "x"
                } else {
                    "y"
                };
                let Val::Obj(o) = value!(kid(0, env)) else {
                    return Outcome::stuck("notIndexable");
                };
                if matches!(t.con, GET_X | GET_Y) {
                    let found =
                        o.0.borrow()
                            .iter()
                            .find(|(l, _)| *l == label)
                            .map(|(_, v)| v.clone());
                    return match found {
                        Some(v) => Value(v),
                        None => Outcome::stuck("propertyNotFound"),
                    };
                }
                let v = value!(kid(1, env));
                let mut fields = o.0.borrow_mut();
                match fields.iter_mut().find(|(l, _)| *l == label) {
                    Some(slot) => {
                        slot.1 = v.clone();
                        Value(v)
                    }
                    None => Outcome::stuck("propertyNotFound"),
                }
            }
            SEQ => {
                value!(kid(0, env));
                kid(1, env)
            }
            NOT => Value(Val::Bool(!value!(kid(0, env)).truthy())),
            TYPEOF => Value(Val::Str(
                match value!(kid(0, env)) {
                    Val::Num(_) => "number",
                    Val::Str(_) => "string",
                    Val::Bool(_) => "boolean",
                    Val::Undefined => "undefined",
                    Val::Null => "object",
                    Val::Clo(_) => "function",
                    Val::Obj(_) => "object",
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
                    // A string doubled call after call outgrows memory long
                    // before the fuel runs out; past a bound, it counts as
                    // out of fuel (the Lean model's driver does the same).
                    (PLUS, Val::Str(x), Val::Str(y)) if x.len() + y.len() > 4096 => {
                        Outcome::Timeout
                    }
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
                let mut inner = vec![Slot::new(v)];
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
                let mut inner: Vec<Slot> = args[..c.arity].iter().cloned().map(Slot::new).collect();
                inner.push(Slot::new(f.clone()));
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
        "model (inty's Lean model, iteration 3: functions, let, assignment)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        let slots: Vec<Slot> = env.iter().cloned().map(Slot::new).collect();
        self.ev(t, &slots, &Cell::new(self.fuel))
    }

    fn same(&self, a: &Val, b: &Val) -> bool {
        a.same(b, 3)
    }

    fn isolate(&self, v: &Val) -> Val {
        v.isolate(6)
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::Num(b) => f64::from_bits(*b).to_string(),
            Val::Str(s) => format!("{s:?}"),
            Val::Bool(b) => b.to_string(),
            Val::Undefined => "undefined".into(),
            Val::Null => "null".into(),
            Val::Clo(c) => format!("fn{}({})", c.arity, self.show_term(&c.body)),
            // Shallow: an object can hold itself.
            Val::Obj(o) => {
                let fields: Vec<String> =
                    o.0.borrow()
                        .iter()
                        .map(|(l, v)| match v {
                            Val::Obj(_) => format!("{l}: {{...}}"),
                            v => format!("{l}: {}", self.show_value(v)),
                        })
                        .collect();
                format!("{{{}}}", fields.join(", "))
            }
        }
    }
}
