//! Heap: storage for mutable cells (objects, arrays, variable boxes).
//!
//! The simplest correct model: a `HashMap<Loc, Cell>` with a monotonic
//! counter handing out fresh `Loc`s. Don't model prototypes — flatten
//! anything that current type rules treat as a simple row.
//!
//! Variable cells (`Cell::Var`) back mutable bindings: assignment to a
//! `var` updates the cell, reads dereference it.

use std::collections::HashMap;

use crate::types::PropName;

use super::value::Value;

/// A heap address.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Loc(pub usize);

/// An object's properties, in the order they were made, as JavaScript
/// keeps them: a spread copies them in that order (running getters as it
/// reaches them), and storing to one that is there keeps its place.
#[derive(Clone, Debug, Default)]
pub struct Props(Vec<(PropName, Value)>);

impl Props {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, name: &PropName) -> Option<&Value> {
        self.0.iter().find(|(k, _)| k == name).map(|(_, v)| v)
    }

    /// Store `value` at `name`: in its place if it is there, else last.
    pub fn insert(&mut self, name: PropName, value: Value) {
        match self.0.iter_mut().find(|(k, _)| *k == name) {
            Some((_, v)) => *v = value,
            None => self.0.push((name, value)),
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = &PropName> {
        self.0.iter().map(|(k, _)| k)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&PropName, &Value)> {
        self.0.iter().map(|(k, v)| (k, v))
    }
}

impl IntoIterator for Props {
    type Item = (PropName, Value);
    type IntoIter = std::vec::IntoIter<(PropName, Value)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Clone, Debug)]
pub enum Cell {
    Object(Props),
    Array(Vec<Value>),
    /// A mutable variable's storage cell. Bare `var` and `let` bindings
    /// resolve to a `Cell::Var` so assignment can update it without
    /// rebuilding the env.
    Var(Value),
}

#[derive(Clone, Debug, Default)]
pub struct Heap {
    cells: HashMap<Loc, Cell>,
    next: usize,
}

impl Heap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc(&mut self, cell: Cell) -> Loc {
        let loc = Loc(self.next);
        self.next += 1;
        self.cells.insert(loc, cell);
        loc
    }

    pub fn get(&self, loc: Loc) -> Option<&Cell> {
        self.cells.get(&loc)
    }

    pub fn get_mut(&mut self, loc: Loc) -> Option<&mut Cell> {
        self.cells.get_mut(&loc)
    }
}
