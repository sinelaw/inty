//! Heap: storage for mutable cells (objects, arrays, variable boxes).
//!
//! The simplest correct model: a `HashMap<Loc, Cell>` with a monotonic
//! counter handing out fresh `Loc`s. Don't model prototypes — flatten
//! anything that current type rules treat as a simple row.
//!
//! Variable cells (`Cell::Var`) back mutable bindings: assignment to a
//! `var` updates the cell, reads dereference it.

use std::collections::{BTreeMap, HashMap};

use crate::types::PropName;

use super::value::Value;

/// A heap address.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Loc(pub usize);

#[derive(Clone, Debug)]
pub enum Cell {
    Object(BTreeMap<PropName, Value>),
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
