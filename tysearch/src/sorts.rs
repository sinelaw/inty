//! Level 1: discover the base types from the values' behaviour.
//!
//! A canonical-forms lemma says which values each eliminator accepts:
//! `if` takes `true` and `false`, `succ` takes numerals. So a value's base
//! type is read off which immediate contexts `c(…, [ ], …)` it gets stuck
//! in, with the context's other positions filled by probe values. Two
//! values with the same fingerprint are in the same sort.
//!
//! Only one-hole contexts one constructor deep are used. Deeper contexts
//! split more finely (`succ(if [ ] then 0 else true)` tells `true` from
//! `false`), down to the full Myhill-Nerode congruence of "doesn't get
//! stuck", which is the exact semantics and not a type system: types
//! deliberately forget which value is which.

use crate::enumerate::product;
use crate::lang::{Language, Outcome, Term};
use std::collections::HashMap;

/// Evaluates through a cache: the corpus evaluates every subterm many times.
pub struct Oracle<'a, L: Language> {
    pub lang: &'a L,
    cache: HashMap<Term, Outcome<L::Value>>,
    pub evals: usize,
}

impl<'a, L: Language> Oracle<'a, L> {
    pub fn new(lang: &'a L) -> Self {
        Oracle {
            lang,
            cache: HashMap::new(),
            evals: 0,
        }
    }

    pub fn eval(&mut self, t: &Term) -> Outcome<L::Value> {
        if let Some(o) = self.cache.get(t) {
            return o.clone();
        }
        self.evals += 1;
        let o = self.lang.eval(t);
        self.cache.insert(t.clone(), o.clone());
        o
    }
}

/// A one-hole context: constructor `con` with the hole at `hole` and the
/// other children `others`, in order.
struct Ctx {
    con: usize,
    hole: usize,
    others: Vec<Term>,
}

impl Ctx {
    fn plug(&self, t: Term) -> Term {
        let mut kids = self.others.clone();
        kids.insert(self.hole, t);
        Term::new(self.con, kids)
    }
}

pub type SortId = usize;

pub struct Sorts<V> {
    contexts: Vec<Ctx>,
    by_print: HashMap<Vec<bool>, SortId>,
    memo: HashMap<V, Option<SortId>>,
    /// Each sort's values from the pool, smallest first.
    pub members: Vec<Vec<V>>,
}

impl<V: Clone + Eq + std::hash::Hash> Sorts<V> {
    /// Partitions `pool` by fingerprint, against contexts filled with
    /// `probes`. Sorts are numbered by their first member in `pool`.
    pub fn discover<L: Language<Value = V>>(
        oracle: &mut Oracle<L>,
        pool: &[V],
        probes: &[V],
    ) -> Self {
        let probe_terms: Vec<Term> = probes.iter().map(|v| oracle.lang.quote(v)).collect();
        let mut contexts = Vec::new();
        for (ci, c) in oracle.lang.signature().iter().enumerate() {
            for hole in 0..c.arity {
                let pools: Vec<&[Term]> = (1..c.arity).map(|_| probe_terms.as_slice()).collect();
                product(&pools, &mut Vec::new(), &mut |others| {
                    contexts.push(Ctx {
                        con: ci,
                        hole,
                        others: others.to_vec(),
                    })
                });
            }
        }
        let mut sorts = Sorts {
            contexts,
            by_print: HashMap::new(),
            memo: HashMap::new(),
            members: Vec::new(),
        };
        for v in pool {
            let print = sorts.fingerprint(oracle, v);
            let next = sorts.by_print.len();
            let id = *sorts.by_print.entry(print).or_insert(next);
            if id == sorts.members.len() {
                sorts.members.push(Vec::new());
            }
            sorts.members[id].push(v.clone());
            sorts.memo.insert(v.clone(), Some(id));
        }
        sorts
    }

    fn fingerprint<L: Language<Value = V>>(&self, oracle: &mut Oracle<L>, v: &V) -> Vec<bool> {
        let t = oracle.lang.quote(v);
        self.contexts
            .iter()
            .map(|ctx| matches!(oracle.eval(&ctx.plug(t.clone())), Outcome::Stuck(_)))
            .collect()
    }

    /// The sort of any value, or `None` if it behaves like no pool value.
    pub fn classify<L: Language<Value = V>>(
        &mut self,
        oracle: &mut Oracle<L>,
        v: &V,
    ) -> Option<SortId> {
        if let Some(s) = self.memo.get(v) {
            return *s;
        }
        let s = self.by_print.get(&self.fingerprint(oracle, v)).copied();
        self.memo.insert(v.clone(), s);
        s
    }

    pub fn count(&self) -> usize {
        self.members.len()
    }

    /// Up to `n` members of `sort`, spread from smallest to largest.
    pub fn samples(&self, sort: SortId, n: usize) -> Vec<V> {
        let m = &self.members[sort];
        if m.len() <= n {
            return m.clone();
        }
        (0..n)
            .map(|i| m[i * (m.len() - 1) / (n - 1).max(1)].clone())
            .collect()
    }
}
