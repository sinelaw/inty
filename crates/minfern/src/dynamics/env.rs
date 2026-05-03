//! Runtime environment: a lexically-scoped name → heap-loc map.
//!
//! Bindings resolve to `Loc`s pointing at `Cell::Var(value)` cells in
//! the heap, not directly to values. This is what makes closures see
//! mutations to a captured variable: the closure snapshot retains the
//! same `Loc`, and reads dereference through the heap.
//!
//! The env itself is immutable persistent (clone-on-extend through an
//! `Rc` chain) so taking a closure snapshot is cheap.

use std::rc::Rc;

use super::heap::Loc;

#[derive(Clone, Debug, Default)]
pub struct RuntimeEnv {
    head: Option<Rc<Frame>>,
}

#[derive(Debug)]
struct Frame {
    name: String,
    loc: Loc,
    next: Option<Rc<Frame>>,
}

impl RuntimeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    /// Extend the env with a new binding. Older bindings of the same
    /// name are shadowed.
    pub fn extend(&self, name: String, loc: Loc) -> Self {
        RuntimeEnv {
            head: Some(Rc::new(Frame {
                name,
                loc,
                next: self.head.clone(),
            })),
        }
    }

    /// Look up a name, returning the most recently bound `Loc`.
    pub fn lookup(&self, name: &str) -> Option<Loc> {
        let mut cursor = self.head.as_deref();
        while let Some(frame) = cursor {
            if frame.name == name {
                return Some(frame.loc);
            }
            cursor = frame.next.as_deref();
        }
        None
    }
}
