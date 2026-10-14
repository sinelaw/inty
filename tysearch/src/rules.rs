//! The hypothesis space: typing rules in a fixed format.
//!
//! A rule for constructor `c` of arity `n` is a schema
//! `c : (P1, …, Pn) -> P0`, each `Pi` a sort or a type variable, a variable
//! shared between positions meaning those types are equal. It reads as the
//! inference rule
//!
//! ```text
//!   ⊢ e1 : P1  …  ⊢ en : Pn
//!   ───────────────────────
//!     ⊢ c(e1, …, en) : P0
//! ```
//!
//! A constructor may have several rules (overloading), or none (the
//! constructor is not typable). This first-order format is the prototype's
//! whole space; DESIGN.md describes the richer ones (contexts and binders,
//! arrows, schemes, rows).

use crate::sorts::SortId;
use std::collections::BTreeSet;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Pat {
    Sort(SortId),
    Var(usize),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Schema {
    pub con: usize,
    pub args: Vec<Pat>,
    pub res: Pat,
}

impl Schema {
    /// The result sort when the children have sorts `kids`, if it applies.
    pub fn apply(&self, kids: &[SortId]) -> Option<SortId> {
        let mut bind: Vec<Option<SortId>> = vec![None; self.vars()];
        for (p, &k) in self.args.iter().zip(kids) {
            match *p {
                Pat::Sort(s) if s != k => return None,
                Pat::Sort(_) => {}
                Pat::Var(v) => match bind[v] {
                    Some(b) if b != k => return None,
                    _ => bind[v] = Some(k),
                },
            }
        }
        match self.res {
            Pat::Sort(s) => Some(s),
            Pat::Var(v) => bind[v],
        }
    }

    pub fn vars(&self) -> usize {
        self.args
            .iter()
            .chain([&self.res])
            .filter_map(|p| match p {
                Pat::Var(v) => Some(v + 1),
                Pat::Sort(_) => None,
            })
            .max()
            .unwrap_or(0)
    }

    /// How many of the `sorts^n` child sort tuples the rule accepts.
    pub fn generality(&self, sorts: usize) -> usize {
        all_tuples(self.args.len(), sorts)
            .iter()
            .filter(|t| self.apply(t).is_some())
            .count()
    }

    /// Sort constants mentioned: the description-length tie-break.
    pub fn constants(&self) -> usize {
        self.args
            .iter()
            .chain([&self.res])
            .filter(|p| matches!(p, Pat::Sort(_)))
            .count()
    }
}

/// Every child sort tuple of length `n`.
pub fn all_tuples(n: usize, sorts: usize) -> Vec<Vec<SortId>> {
    let mut out = vec![Vec::new()];
    for _ in 0..n {
        out = out
            .into_iter()
            .flat_map(|t| {
                (0..sorts).map(move |s| {
                    let mut t = t.clone();
                    t.push(s);
                    t
                })
            })
            .collect();
    }
    out
}

/// Every schema for a constructor of arity `n` over `sorts` sorts, with
/// variables numbered in order of first appearance (so no two schemas are
/// equal up to renaming) and the result's variable bound by an argument.
pub fn enumerate_schemas(con: usize, n: usize, sorts: usize) -> Vec<Schema> {
    fn go(n: usize, sorts: usize, acc: &mut Vec<Pat>, next_var: usize, out: &mut Vec<Vec<Pat>>) {
        if acc.len() == n + 1 {
            out.push(acc.clone());
            return;
        }
        let is_res = acc.len() == n;
        for s in 0..sorts {
            acc.push(Pat::Sort(s));
            go(n, sorts, acc, next_var, out);
            acc.pop();
        }
        let fresh = if is_res { next_var } else { next_var + 1 };
        for v in 0..fresh {
            acc.push(Pat::Var(v));
            go(n, sorts, acc, next_var.max(v + 1), out);
            acc.pop();
        }
    }
    let mut out = Vec::new();
    go(n, sorts, &mut Vec::new(), 0, &mut out);
    out.into_iter()
        .map(|mut ps| {
            let res = ps.pop().unwrap();
            Schema { con, args: ps, res }
        })
        .collect()
}

/// A rule set, and the type checker it induces on closed terms.
#[derive(Clone, Debug, Default)]
pub struct RuleSet {
    pub rules: Vec<Schema>,
}

impl RuleSet {
    /// The sorts a term can be given, bottom up. The format makes this at
    /// most one sort for every term but those overloaded rules type twice.
    pub fn type_of(&self, t: &crate::lang::Term) -> BTreeSet<SortId> {
        let kids: Vec<BTreeSet<SortId>> = t.kids.iter().map(|k| self.type_of(k)).collect();
        let mut out = BTreeSet::new();
        for r in self.rules.iter().filter(|r| r.con == t.con) {
            let pools: Vec<Vec<SortId>> =
                kids.iter().map(|k| k.iter().copied().collect()).collect();
            let refs: Vec<&[SortId]> = pools.iter().map(|p| p.as_slice()).collect();
            crate::enumerate::product(&refs, &mut Vec::new(), &mut |ks| {
                if let Some(s) = r.apply(ks) {
                    out.insert(s);
                }
            });
        }
        out
    }
}

/// The least general schema above all of `rules` (Plotkin's
/// anti-unification), and the sort tuples its variables stood for. Where
/// overloaded rules differ only in which sort runs through them, this is
/// a type class: `+ : (a, a) -> a` where `a ∈ {num, str}`.
pub fn anti_unify(rules: &[Schema]) -> (Schema, Vec<Vec<SortId>>) {
    let n = rules[0].args.len();
    let mut columns: Vec<Vec<Pat>> = Vec::new();
    let mut out = Vec::new();
    for i in 0..=n {
        let col: Vec<Pat> = rules
            .iter()
            .map(|r| if i < n { r.args[i] } else { r.res })
            .collect();
        if col.iter().all(|p| *p == col[0]) {
            out.push(col[0]);
        } else {
            let v = columns.iter().position(|c| *c == col).unwrap_or_else(|| {
                columns.push(col.clone());
                columns.len() - 1
            });
            out.push(Pat::Var(v));
        }
    }
    let res = out.pop().unwrap();
    let mut instances: Vec<Vec<SortId>> = (0..rules.len())
        .map(|r| {
            columns
                .iter()
                .map(|c| match c[r] {
                    Pat::Sort(s) => s,
                    Pat::Var(_) => usize::MAX,
                })
                .collect()
        })
        .collect();
    instances.sort();
    (
        Schema {
            con: rules[0].con,
            args: out,
            res,
        },
        instances,
    )
}

/// Prints a schema with sort names and `a`, `b`, … for variables.
pub struct Show<'a> {
    pub schema: &'a Schema,
    pub con: &'a str,
    pub sort_names: &'a [String],
}

impl fmt::Display for Show<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let p = |p: &Pat| match *p {
            Pat::Sort(s) => self.sort_names[s].clone(),
            Pat::Var(v) => ((b'a' + v as u8) as char).to_string(),
        };
        let args: Vec<String> = self.schema.args.iter().map(p).collect();
        if args.is_empty() {
            write!(f, "{} : {}", self.con, p(&self.schema.res))
        } else {
            write!(
                f,
                "{} : ({}) -> {}",
                self.con,
                args.join(", "),
                p(&self.schema.res)
            )
        }
    }
}
