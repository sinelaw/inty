//! What the search is given: a language as a black box.
//!
//! A language is a signature (its term constructors) and an evaluator that
//! says what a closed term does: a value, stuck, an allowed fault, or out of
//! fuel. Nothing else about the semantics is visible to the search, so the
//! same machinery runs on a toy interpreter, on inty's `dynamics`, or on the
//! Lean model behind a process boundary.

use std::fmt;
use std::hash::Hash;

/// A literal's payload: the number in `3`, the text in `"a"`.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Atom {
    None,
    Int(i64),
    Str(String),
}

/// A closed first-order term: a constructor, its payload and its children.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Term {
    pub con: usize,
    pub atom: Atom,
    pub kids: Vec<Term>,
}

impl Term {
    pub fn new(con: usize, kids: Vec<Term>) -> Term {
        Term {
            con,
            atom: Atom::None,
            kids,
        }
    }

    pub fn leaf(con: usize, atom: Atom) -> Term {
        Term {
            con,
            atom,
            kids: Vec::new(),
        }
    }

    pub fn size(&self) -> usize {
        1 + self.kids.iter().map(Term::size).sum::<usize>()
    }
}

/// A term constructor. A literal family (`num`, `str`) has arity 0 and the
/// payloads the enumerator tries; every other constructor has none.
#[derive(Clone, Debug)]
pub struct Con {
    pub name: &'static str,
    pub arity: usize,
    pub atoms: Vec<Atom>,
}

impl Con {
    pub fn op(name: &'static str, arity: usize) -> Con {
        Con {
            name,
            arity,
            atoms: Vec::new(),
        }
    }

    pub fn literal(name: &'static str, atoms: Vec<Atom>) -> Con {
        Con {
            name,
            arity: 0,
            atoms,
        }
    }

    /// The payloads to enumerate: the literal's, or the one empty payload.
    pub fn atoms_or_none(&self) -> Vec<Atom> {
        if self.atoms.is_empty() {
            vec![Atom::None]
        } else {
            self.atoms.clone()
        }
    }
}

/// What running a closed term does.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Outcome<V> {
    Value(V),
    /// No rule applies: the thing a type system must rule out.
    Stuck(String),
    /// A failure the language documents as allowed (an index out of bounds,
    /// an uncaught `throw`): safe for every type, as in inty's model.
    Fault(String),
    /// Out of fuel: says nothing either way.
    Timeout,
}

/// A language under study.
pub trait Language {
    type Value: Clone + Eq + Hash + fmt::Debug;

    fn name(&self) -> &str;
    fn signature(&self) -> &[Con];
    fn eval(&self, t: &Term) -> Outcome<Self::Value>;
    /// A term that evaluates to `v`, to plug values into contexts.
    fn quote(&self, v: &Self::Value) -> Term;

    fn show_value(&self, v: &Self::Value) -> String {
        self.show_term(&self.quote(v))
    }

    fn show_term(&self, t: &Term) -> String {
        let c = &self.signature()[t.con];
        let head = match &t.atom {
            Atom::None => c.name.to_string(),
            Atom::Int(n) => n.to_string(),
            Atom::Str(s) => format!("{s:?}"),
        };
        if t.kids.is_empty() {
            head
        } else {
            let kids: Vec<String> = t.kids.iter().map(|k| self.show_term(k)).collect();
            format!("{head}({})", kids.join(", "))
        }
    }
}
