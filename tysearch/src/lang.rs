//! What the search is given: a language as a black box.
//!
//! A language is a signature (its term constructors, and which children
//! bind variables) and an evaluator that runs a term in an environment of
//! values: to a value, stuck, an allowed fault, or out of fuel. Nothing
//! else about the semantics is visible to the search, so the same
//! machinery runs on a toy interpreter, on inty's `dynamics`, or on the
//! Lean model behind a process boundary.
//!
//! Variables are de Bruijn indices, as in the Lean model: `var(i)` is
//! `env[i]`, `env[0]` the innermost binding.

use std::fmt;
use std::hash::Hash;

/// A literal's payload: the number in `3`, the text in `"a"`, the index
/// of a variable.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Atom {
    None,
    Int(i64),
    Str(String),
}

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

/// What kind of constructor: an ordinary one, whose typing rule the search
/// looks for; the variable, whose rule (look the variable up in the
/// context) every type system with binders shares; or assignment to the
/// variable its payload names, `x = e`, whose rule is as fixed: `e` has
/// the variable's type, which must not be generalised.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Op,
    Var,
    Assign,
}

/// A term constructor. A literal family (`num`, `str`) has arity 0 and the
/// payloads the enumerator tries. `binds[i]` is how many variables child
/// `i` sees bound: `var(0)` .. `var(binds[i] - 1)`.
#[derive(Clone, Debug)]
pub struct Con {
    pub name: &'static str,
    pub arity: usize,
    pub binds: Vec<usize>,
    pub atoms: Vec<Atom>,
    pub kind: Kind,
}

impl Con {
    pub fn op(name: &'static str, arity: usize) -> Con {
        Con {
            name,
            arity,
            binds: vec![0; arity],
            atoms: Vec::new(),
            kind: Kind::Op,
        }
    }

    /// A constructor whose children bind `binds[i]` variables each.
    pub fn binder(name: &'static str, binds: Vec<usize>) -> Con {
        Con {
            name,
            arity: binds.len(),
            binds,
            atoms: Vec::new(),
            kind: Kind::Op,
        }
    }

    pub fn literal(name: &'static str, atoms: Vec<Atom>) -> Con {
        Con {
            name,
            arity: 0,
            binds: Vec::new(),
            atoms,
            kind: Kind::Op,
        }
    }

    pub fn var() -> Con {
        Con {
            name: "var",
            arity: 0,
            binds: Vec::new(),
            atoms: Vec::new(),
            kind: Kind::Var,
        }
    }

    /// `x_i = e`, the variable's index as the payload.
    pub fn assign() -> Con {
        Con {
            name: "assign",
            arity: 1,
            binds: vec![0],
            atoms: Vec::new(),
            kind: Kind::Assign,
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

/// What running a term does.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Outcome<V> {
    Value(V),
    /// No rule applies: the thing a type system must rule out. `root` says
    /// whether the term's own constructor got stuck, on its children's
    /// values, rather than something it ran (a child, or a called
    /// function's body). Canonical forms are about the first kind.
    Stuck {
        reason: String,
        root: bool,
    },
    /// A failure the language documents as allowed (an index out of
    /// bounds, an uncaught `throw`): safe for every type, as in inty's
    /// model.
    Fault(String),
    /// Out of fuel: says nothing either way.
    Timeout,
}

impl<V> Outcome<V> {
    pub fn stuck(reason: impl Into<String>) -> Self {
        Outcome::Stuck {
            reason: reason.into(),
            root: true,
        }
    }

    /// The same outcome seen from an enclosing term: a stuck child is not
    /// the enclosing term's own.
    pub fn from_inside(self) -> Self {
        match self {
            Outcome::Stuck { reason, .. } => Outcome::Stuck {
                reason,
                root: false,
            },
            o => o,
        }
    }

    pub fn is_stuck(&self) -> bool {
        matches!(self, Outcome::Stuck { .. })
    }
}

/// A language under study.
pub trait Language {
    type Value: Clone + Eq + Hash + fmt::Debug;

    fn name(&self) -> &str;
    fn signature(&self) -> &[Con];
    /// Runs `t` with `var(i)` bound to `env[i]`.
    fn eval_in(&self, t: &Term, env: &[Self::Value]) -> Outcome<Self::Value>;
    fn show_value(&self, v: &Self::Value) -> String;

    fn eval(&self, t: &Term) -> Outcome<Self::Value> {
        self.eval_in(t, &[])
    }

    /// A copy of `v` with state of its own: new cells holding copies of the
    /// old ones' contents. Each run the search makes starts from copies, so
    /// what one run stores can't leak into the next, or into the pool of
    /// values the search keeps (a test that stores into a reference
    /// shouldn't change the reference everyone else samples).
    fn isolate(&self, v: &Self::Value) -> Self::Value {
        v.clone()
    }

    /// Whether two values are the same as far as the search can tell: `==`
    /// unless the language's values have identity (cells) that `==` sees
    /// and the search shouldn't (two closures made by two runs of one
    /// term are the same closure).
    fn same(&self, a: &Self::Value, b: &Self::Value) -> bool {
        a == b
    }

    fn same_outcome(&self, a: &Outcome<Self::Value>, b: &Outcome<Self::Value>) -> bool {
        match (a, b) {
            (Outcome::Value(x), Outcome::Value(y)) => self.same(x, y),
            (a, b) => a == b,
        }
    }

    fn show_term(&self, t: &Term) -> String {
        let c = &self.signature()[t.con];
        let head = match (&t.atom, c.kind) {
            (Atom::Int(n), Kind::Var) => format!("x{n}"),
            (Atom::Int(n), Kind::Assign) => format!("x{n} ="),
            (Atom::None, _) => c.name.to_string(),
            (Atom::Int(n), _) => n.to_string(),
            (Atom::Str(s), _) => format!("{s:?}"),
        };
        if t.kids.is_empty() {
            head
        } else {
            let kids: Vec<String> = t.kids.iter().map(|k| self.show_term(k)).collect();
            format!("{head}({})", kids.join(", "))
        }
    }

    /// The constructor named `name`.
    fn con(&self, name: &str) -> usize {
        self.signature()
            .iter()
            .position(|c| c.name == name)
            .unwrap_or_else(|| panic!("no constructor {name}"))
    }
}
