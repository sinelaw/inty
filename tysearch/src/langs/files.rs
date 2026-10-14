//! Typestate: a file is open or closed, `read` and `close` need it open,
//! and `close` changes it. The same value has a different type before and
//! after: a type system for it must track that through the program (or
//! make files linear). The rule format types each value once, so this
//! measures what the search makes of it.

use crate::lang::{Atom, Con, Language, Outcome, Term};
use std::cell::Cell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub struct Files {
    sig: Vec<Con>,
}

const OPEN: usize = 0;
const READ: usize = 1;
const CLOSE: usize = 2;
const STR: usize = 3;
const CONCAT: usize = 4;
const LET: usize = 5;
const SEQ: usize = 6;
const VAR: usize = 7;

/// A file handle: open or not. Equal only if the same handle.
#[derive(Clone, Debug)]
pub struct Handle(Rc<Cell<bool>>);

impl PartialEq for Handle {
    fn eq(&self, other: &Handle) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Handle {}

impl Hash for Handle {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(h)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Val {
    File(Handle),
    Str(String),
}

impl Default for Files {
    fn default() -> Self {
        Files {
            sig: vec![
                Con::op("open", 0),
                Con::op("read", 1),
                Con::op("close", 1),
                Con::literal("str", vec![Atom::Str(String::new()), Atom::Str("a".into())]),
                Con::op("++", 2),
                Con::binder("let", vec![0, 1]),
                Con::op("seq", 2),
                Con::var(),
            ],
        }
    }
}

impl Files {
    fn ev(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        use Outcome::Value;
        let kid = |i: usize, env: &[Val]| self.ev(&t.kids[i], env).from_inside();
        macro_rules! value {
            ($e:expr) => {
                match $e {
                    Value(v) => v,
                    other => return other,
                }
            };
        }
        match (t.con, &t.atom) {
            (VAR, Atom::Int(i)) => match env.get(*i as usize) {
                Some(v) => Value(v.clone()),
                None => Outcome::stuck("unbound"),
            },
            (OPEN, _) => Value(Val::File(Handle(Rc::new(Cell::new(true))))),
            (READ, _) => match value!(kid(0, env)) {
                Val::File(h) if h.0.get() => Value(Val::Str("data".into())),
                Val::File(_) => Outcome::stuck("read of a closed file"),
                _ => Outcome::stuck("not a file"),
            },
            (CLOSE, _) => match value!(kid(0, env)) {
                Val::File(h) if h.0.get() => {
                    h.0.set(false);
                    Value(Val::File(h))
                }
                Val::File(_) => Outcome::stuck("close of a closed file"),
                _ => Outcome::stuck("not a file"),
            },
            (STR, Atom::Str(s)) => Value(Val::Str(s.clone())),
            (CONCAT, _) => match (value!(kid(0, env)), value!(kid(1, env))) {
                (Val::Str(a), Val::Str(b)) if a.len() + b.len() <= 64 => Value(Val::Str(a + &b)),
                (Val::Str(_), Val::Str(_)) => Outcome::Timeout,
                _ => Outcome::stuck("not strings"),
            },
            (LET, _) => {
                let v = value!(kid(0, env));
                let mut inner = vec![v];
                inner.extend_from_slice(env);
                kid(1, &inner)
            }
            (SEQ, _) => {
                value!(kid(0, env));
                kid(1, env)
            }
            _ => unreachable!(),
        }
    }
}

impl Language for Files {
    type Value = Val;

    fn name(&self) -> &str {
        "files (typestate: open, read, close)"
    }

    fn signature(&self) -> &[Con] {
        &self.sig
    }

    fn eval_in(&self, t: &Term, env: &[Val]) -> Outcome<Val> {
        self.ev(t, env)
    }

    fn same(&self, a: &Val, b: &Val) -> bool {
        match (a, b) {
            (Val::File(x), Val::File(y)) => x.0.get() == y.0.get(),
            (a, b) => a == b,
        }
    }

    fn isolate(&self, v: &Val) -> Val {
        match v {
            Val::File(h) => Val::File(Handle(Rc::new(Cell::new(h.0.get())))),
            v => v.clone(),
        }
    }

    fn show_value(&self, v: &Val) -> String {
        match v {
            Val::File(h) if h.0.get() => "<open file>".into(),
            Val::File(_) => "<closed file>".into(),
            Val::Str(s) => format!("{s:?}"),
        }
    }
}
