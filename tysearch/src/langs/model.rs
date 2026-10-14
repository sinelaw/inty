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
//! stored with `.x =` (iteration 5); and arrays, indexed as the model's
//! `Value.index` and `Value.setIndex` do (iteration 6); and `throw`,
//! `try`/`catch`, `while`, `break` and `continue` (iteration 7); and
//! `return` (iteration 8); and `typeof` tests that narrow (iteration 10).
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
const ARR1: usize = 30;
const ARR2: usize = 31;
const IDX: usize = 32;
const SET_IDX: usize = 33;
const THROW: usize = 34;
const TRY: usize = 35;
const WHILE: usize = 36;
const BREAK: usize = 37;
const CONTINUE: usize = 38;
const RET: usize = 39;
const IS_NUM: usize = 40;
const IS_STR: usize = 41;

/// A run's state besides the store: the fuel left, and the value a `throw`
/// is carrying to its `try`.
struct Run {
    fuel: Cell<usize>,
    thrown: RefCell<Option<Val>>,
}

/// Abrupt completions travel as faults, which every construct but their
/// catcher passes on, and which are allowed at the top, as in the Lean
/// model's `Result.Abrupt`: an uncaught `throw`, or a `break` or `continue`
/// outside a loop.
const THROWN: &str = "uncaughtThrow";
const BROKE: &str = "break";
const CONTINUED: &str = "continue";

/// An array's cell: its elements. Equal only if the same cell.
#[derive(Clone)]
pub struct ArrCell(Rc<RefCell<Vec<Val>>>);

impl std::fmt::Debug for ArrCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "arr@{:p}", Rc::as_ptr(&self.0))
    }
}

impl PartialEq for ArrCell {
    fn eq(&self, other: &ArrCell) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for ArrCell {}

impl Hash for ArrCell {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(h)
    }
}

/// A number as an array index: a non-negative integer.
fn to_index(bits: u64) -> Option<usize> {
    let n = f64::from_bits(bits);
    (n >= 0.0 && n.fract() == 0.0 && n < 1e9).then_some(n as usize)
}

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
    Arr(ArrCell),
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
            (Val::Arr(a), Val::Arr(b)) => {
                a == b || {
                    let (x, y) = (a.0.borrow(), b.0.borrow());
                    x.len() == y.len()
                        && (depth == 0 || x.iter().zip(y.iter()).all(|(v, w)| v.same(w, depth - 1)))
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
            Val::Arr(a) if depth > 0 => Val::Arr(ArrCell(Rc::new(RefCell::new(
                a.0.borrow().iter().map(|v| v.isolate(depth - 1)).collect(),
            )))),
            Val::Obj(o) if depth > 0 => Val::Obj(ObjCell(Rc::new(RefCell::new(
                o.0.borrow()
                    .iter()
                    .map(|(l, v)| (*l, v.isolate(depth - 1)))
                    .collect(),
            )))),
            v => v.clone(),
        }
    }

    /// What `typeof` says, as `Value.typeString` in the model.
    fn type_string(&self) -> &'static str {
        match self {
            Val::Num(_) => "number",
            Val::Str(_) => "string",
            Val::Bool(_) => "boolean",
            Val::Undefined => "undefined",
            Val::Null => "object",
            Val::Clo(_) => "function",
            Val::Obj(_) | Val::Arr(_) => "object",
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
            Val::Clo(_) | Val::Obj(_) | Val::Arr(_) => true,
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
                Con::op("[a]", 1),
                Con::op("[a,b]", 2),
                Con::op("idx", 2),
                Con::op("idx=", 3),
                Con::op("throw", 1),
                Con::binder("try", vec![0, 1]),
                Con::op("while", 2),
                Con::op("break", 0),
                Con::op("continue", 0),
                Con::op("return", 1),
                Con::binder("typeof=number", vec![0, 1, 1]),
                Con::binder("typeof=string", vec![0, 1, 1]),
            ],
            fuel: 64,
        }
    }
}

impl Model {
    fn ev(&self, t: &Term, env: &[Slot], run: &Run) -> Outcome<Val> {
        use Outcome::Value;
        let kid = |i: usize, env: &[Slot]| self.ev(&t.kids[i], env, run).from_inside();
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
                // As the model's `setProp`: a property the object has keeps
                // its place; one it hasn't is added.
                let v = value!(kid(1, env));
                let mut fields = o.0.borrow_mut();
                match fields.iter_mut().find(|(l, _)| *l == label) {
                    Some(slot) => slot.1 = v.clone(),
                    None => fields.push((label, v.clone())),
                }
                Value(v)
            }
            ARR1 | ARR2 => {
                let mut items = Vec::new();
                for i in 0..t.kids.len() {
                    items.push(value!(kid(i, env)));
                }
                Value(Val::Arr(ArrCell(Rc::new(RefCell::new(items)))))
            }
            // As the model's `Value.index`: an array's or a string's element,
            // a fault at an index it hasn't; an object's property by name,
            // or `undefined`.
            IDX => {
                let o = value!(kid(0, env));
                let i = value!(kid(1, env));
                match (&o, &i) {
                    (Val::Arr(a), Val::Num(n)) => {
                        match to_index(*n).and_then(|k| a.0.borrow().get(k).cloned()) {
                            Some(v) => Value(v),
                            None => Outcome::Fault("outOfBounds".into()),
                        }
                    }
                    (Val::Str(s), Val::Num(n)) => match to_index(*n).and_then(|k| s.chars().nth(k))
                    {
                        Some(c) => Value(Val::Str(c.to_string())),
                        None => Outcome::Fault("outOfBounds".into()),
                    },
                    (Val::Obj(o), Val::Str(k)) => Value(
                        o.0.borrow()
                            .iter()
                            .find(|(l, _)| l == k)
                            .map_or(Val::Undefined, |(_, v)| v.clone()),
                    ),
                    (Val::Obj(_), Val::Num(_)) => Value(Val::Undefined),
                    _ => Outcome::stuck("notIndexable"),
                }
            }
            // As the model's `Value.setIndex`: in bounds, or just past the
            // end (a push); a fault further.
            SET_IDX => {
                let o = value!(kid(0, env));
                let i = value!(kid(1, env));
                let v = value!(kid(2, env));
                match (&o, &i) {
                    (Val::Arr(a), Val::Num(n)) => {
                        let mut items = a.0.borrow_mut();
                        match to_index(*n) {
                            Some(k) if k < items.len() => {
                                items[k] = v.clone();
                                Value(v)
                            }
                            Some(k) if k == items.len() && k < 64 => {
                                items.push(v.clone());
                                Value(v)
                            }
                            _ => Outcome::Fault("outOfBounds".into()),
                        }
                    }
                    _ => Outcome::stuck("badAssignmentTarget"),
                }
            }
            SEQ => {
                value!(kid(0, env));
                kid(1, env)
            }
            NOT => Value(Val::Bool(!value!(kid(0, env)).truthy())),
            TYPEOF => Value(Val::Str(value!(kid(0, env)).type_string().into())),
            // As the model's `caseTag e₁ .typeOf t e₂ e₃`: `e₃` if `e₁`'s
            // `typeof` is `t`, else `e₂`, each with the value as `var 0`.
            IS_NUM | IS_STR => {
                let v = value!(kid(0, env));
                let tag = if t.con == IS_NUM { "number" } else { "string" };
                let branch = if v.type_string() == tag { 2 } else { 1 };
                let mut inner = vec![Slot::new(v)];
                inner.extend_from_slice(env);
                kid(branch, &inner)
            }
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
                if run.fuel.get() == 0 {
                    return Outcome::Timeout;
                }
                run.fuel.set(run.fuel.get() - 1);
                // Extra arguments are ignored, as in JavaScript.
                let mut inner: Vec<Slot> = args[..c.arity].iter().cloned().map(Slot::new).collect();
                inner.push(Slot::new(f.clone()));
                inner.extend_from_slice(&c.env);
                // A call turns its body's `return` into its value.
                match self.ev(&c.body, &inner, run).from_inside() {
                    Outcome::Return(v) => Value(v),
                    o => o,
                }
            }
            RET => Outcome::Return(value!(kid(0, env))),
            THROW => {
                let v = value!(kid(0, env));
                let what = format!("{THROWN} {}", self.show_value(&v));
                *run.thrown.borrow_mut() = Some(v);
                Outcome::Fault(what)
            }
            // The caught value goes in a new cell, as `var 0`.
            TRY => match kid(0, env) {
                Outcome::Fault(f) if f.starts_with(THROWN) => {
                    let v = run.thrown.borrow_mut().take().expect("a throw's value");
                    let mut inner = vec![Slot::new(v)];
                    inner.extend_from_slice(env);
                    kid(1, &inner)
                }
                o => o,
            },
            // Each iteration takes a tick, as a call does. A `break` leaves
            // the loop with `undefined`.
            WHILE => loop {
                if !value!(kid(0, env)).truthy() {
                    return Value(Val::Undefined);
                }
                match kid(1, env) {
                    Value(_) => {}
                    Outcome::Fault(f) if f == CONTINUED => {}
                    Outcome::Fault(f) if f == BROKE => return Value(Val::Undefined),
                    o => return o,
                }
                if run.fuel.get() == 0 {
                    return Outcome::Timeout;
                }
                run.fuel.set(run.fuel.get() - 1);
            },
            BREAK => Outcome::Fault(BROKE.into()),
            CONTINUE => Outcome::Fault(CONTINUED.into()),
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
        self.ev(
            t,
            &slots,
            &Run {
                fuel: Cell::new(self.fuel),
                thrown: RefCell::new(None),
            },
        )
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
            Val::Arr(a) => {
                let items: Vec<String> =
                    a.0.borrow()
                        .iter()
                        .map(|v| match v {
                            Val::Arr(_) | Val::Obj(_) => "...".to_string(),
                            v => self.show_value(v),
                        })
                        .collect();
                format!("[{}]", items.join(", "))
            }
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
