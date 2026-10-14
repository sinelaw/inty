//! What types mean: discovered from the values' behaviour.
//!
//! **Sorts.** A canonical-forms lemma says which values each eliminator
//! accepts: `if` takes booleans, `-` numbers, a call functions of enough
//! parameters. So a value's sort is read off which immediate contexts
//! `c(…, [ ], …)` it gets stuck in *at the root*, the other positions
//! filled by probe values. Two values with the same fingerprint share a
//! sort. Only one-hole contexts one constructor deep count, and only the
//! context's own step: a closure that gets stuck inside its body was still
//! accepted by the call. (All contexts would give the Myhill-Nerode
//! congruence of "doesn't get stuck", which is the exact semantics, not a
//! type system.)
//!
//! **Refined sorts.** A sort whose eliminator's result depends on which
//! member it is, beyond the sorts of the other arguments, carries code:
//! `app1(f, 0)` is a number for one closure and a string for another. Such
//! a sort is refined by what its eliminator gives: `T3<A -> R>` is the
//! members that, given arguments of types `A`, run to an `R`. For
//! closures under application that is the function type, found rather than
//! given; its meaning is the logical relation's.
//!
//! **Membership** of a value in a type is tested: by fingerprint for a
//! sort, and for a refined sort by running the eliminator on sampled
//! members of the argument types.

use crate::enumerate::product;
use crate::lang::{Atom, Kind, Language, Outcome, Term};
use crate::types::Ty;
use std::collections::HashMap;

/// A term and the environment it runs in.
type Run<V> = (Term, Vec<V>);

/// Evaluates through a cache: the same term in the same environment comes
/// up again and again.
pub struct Oracle<'a, L: Language> {
    pub lang: &'a L,
    cache: HashMap<Run<L::Value>, Outcome<L::Value>>,
    pub evals: usize,
    /// Whether to remember outcomes: worth it only for languages whose
    /// runs cost more than hashing a term and its environment.
    pub caching: bool,
}

impl<'a, L: Language> Oracle<'a, L> {
    pub fn new(lang: &'a L) -> Self {
        Oracle {
            lang,
            cache: HashMap::new(),
            evals: 0,
            caching: std::env::var_os("TYSEARCH_CACHE").is_some(),
        }
    }

    pub fn eval_in(&mut self, t: &Term, env: &[L::Value]) -> Outcome<L::Value> {
        self.evals += 1;
        if !self.caching {
            return self.lang.eval_in(t, env);
        }
        let key = (t.clone(), env.to_vec());
        if let Some(o) = self.cache.get(&key) {
            return o.clone();
        }
        let o = self.lang.eval_in(t, env);
        self.cache.insert(key, o.clone());
        o
    }

    pub fn eval(&mut self, t: &Term) -> Outcome<L::Value> {
        self.eval_in(t, &[])
    }
}

/// A one-hole context: `term` with the hole as the value of `var(0)` and
/// the probes as `var(1)`, … (each shifted under its child's binders).
struct Ctx<V> {
    con: usize,
    hole: usize,
    term: Term,
    probes: Vec<V>,
}

/// How a refined sort is eliminated: `term` mentions the member as
/// `var(0)` and the other arguments as `var(1)` … `var(k)`.
#[derive(Clone, Debug)]
pub struct Template {
    pub elim: usize,
    pub hole: usize,
    pub k: usize,
    pub term: Term,
}

pub struct Semantics<V> {
    contexts: Vec<Ctx<V>>,
    by_print: HashMap<Vec<bool>, usize>,
    sort_memo: HashMap<V, Option<usize>>,
    holds_memo: HashMap<(V, Ty), bool>,
    samples_memo: HashMap<Ty, Vec<V>>,
    behaviour_memo: HashMap<V, Vec<i64>>,
    /// Values per sort, smallest first.
    pub members: Vec<Vec<V>>,
    /// Per sort, how it's refined, if it is.
    pub templates: Vec<Option<Template>>,
    /// The ground types observation ranges over: the unrefined sorts, and
    /// the refined ones one level deep, those with a member in the pool.
    pub universe: Vec<Ty>,
    pub samples_per_type: usize,
}

/// Builds `con` with child `hole` the variable `var(0)` and the others
/// `var(1)`, `var(2)`, …, each shifted past its child's binders.
fn plug(sig: &[crate::lang::Con], con: usize, hole: usize) -> Term {
    let c = &sig[con];
    let var = sig.iter().position(|c| c.kind == Kind::Var).unwrap();
    let mut next = 1;
    let kids = (0..c.arity)
        .map(|j| {
            let i = if j == hole {
                0
            } else {
                next += 1;
                next - 1
            };
            Term::leaf(var, Atom::Int((i + c.binds[j]) as i64))
        })
        .collect();
    Term::new(con, kids)
}

impl<V: Clone + Eq + std::hash::Hash + std::fmt::Debug> Semantics<V> {
    pub fn discover<L: Language<Value = V>>(
        oracle: &mut Oracle<L>,
        pool: &[V],
        probes: &[V],
        samples_per_type: usize,
    ) -> Self {
        let sig = oracle.lang.signature();
        let has_var = sig.iter().any(|c| c.kind == Kind::Var);
        let mut contexts = Vec::new();
        for (ci, c) in sig.iter().enumerate() {
            if c.kind == Kind::Var || c.arity == 0 || !has_var {
                continue;
            }
            for hole in 0..c.arity {
                let term = plug(sig, ci, hole);
                let pools: Vec<&[V]> = (1..c.arity).map(|_| probes).collect();
                product(&pools, &mut Vec::new(), &mut |ps| {
                    contexts.push(Ctx {
                        con: ci,
                        hole,
                        term: term.clone(),
                        probes: ps.to_vec(),
                    })
                });
            }
        }
        let mut sem = Semantics {
            contexts,
            by_print: HashMap::new(),
            sort_memo: HashMap::new(),
            holds_memo: HashMap::new(),
            samples_memo: HashMap::new(),
            behaviour_memo: HashMap::new(),
            members: Vec::new(),
            templates: Vec::new(),
            universe: Vec::new(),
            samples_per_type,
        };
        for v in pool {
            let print = sem.fingerprint(oracle, v);
            let next = sem.by_print.len();
            let id = *sem.by_print.entry(print).or_insert(next);
            if id == sem.members.len() {
                sem.members.push(Vec::new());
            }
            sem.members[id].push(v.clone());
            sem.sort_memo.insert(v.clone(), Some(id));
        }
        sem.templates = (0..sem.members.len())
            .map(|s| sem.refinement(oracle, s))
            .collect();
        sem.universe = sem.build_universe(oracle);
        sem
    }

    fn env(v: &V, rest: &[V]) -> Vec<V> {
        let mut env = vec![v.clone()];
        env.extend(rest.iter().cloned());
        env
    }

    fn fingerprint<L: Language<Value = V>>(&self, oracle: &mut Oracle<L>, v: &V) -> Vec<bool> {
        self.contexts
            .iter()
            .map(|ctx| {
                matches!(
                    oracle.eval_in(&ctx.term, &Self::env(v, &ctx.probes)),
                    Outcome::Stuck { root: true, .. }
                )
            })
            .collect()
    }

    /// The sort of any value, or `None` if it behaves like no pool value.
    pub fn sort<L: Language<Value = V>>(&mut self, oracle: &mut Oracle<L>, v: &V) -> Option<usize> {
        if let Some(s) = self.sort_memo.get(v) {
            return *s;
        }
        let s = self.by_print.get(&self.fingerprint(oracle, v)).copied();
        self.sort_memo.insert(v.clone(), s);
        s
    }

    pub fn count(&self) -> usize {
        self.members.len()
    }

    /// The first context, in signature order, that accepts the sort's
    /// members and whose result's sort depends on the member although the
    /// other arguments all have one sort.
    fn refinement<L: Language<Value = V>>(
        &mut self,
        oracle: &mut Oracle<L>,
        s: usize,
    ) -> Option<Template> {
        let members: Vec<V> = self.spread(&self.members[s].clone(), 8);
        for i in 0..self.contexts.len() {
            let (con, hole, term, probes) = {
                let c = &self.contexts[i];
                (c.con, c.hole, c.term.clone(), c.probes.clone())
            };
            let probe_sorts: Vec<Option<usize>> =
                probes.iter().map(|p| self.sort(oracle, p)).collect();
            if probe_sorts.windows(2).any(|w| w[0] != w[1]) {
                continue;
            }
            let mut results = Vec::new();
            for m in &members {
                let r = match oracle.eval_in(&term, &Self::env(m, &probes)) {
                    Outcome::Stuck { root: true, .. } => None,
                    Outcome::Value(w) => Some(self.sort(oracle, &w).map_or(-3, |s| s as i64)),
                    Outcome::Stuck { .. } => Some(-1),
                    Outcome::Fault(_) => Some(-2),
                    Outcome::Timeout => continue,
                };
                results.push(r);
            }
            if results.iter().any(Option::is_none) {
                continue;
            }
            results.sort();
            results.dedup();
            if results.len() > 1 {
                return Some(Template {
                    elim: con,
                    hole,
                    k: oracle.lang.signature()[con].arity - 1,
                    term,
                });
            }
        }
        None
    }

    fn build_universe<L: Language<Value = V>>(&mut self, oracle: &mut Oracle<L>) -> Vec<Ty> {
        let base: Vec<Ty> = (0..self.count())
            .filter(|&s| self.templates[s].is_none())
            .map(Ty::Base)
            .collect();
        let mut out = base.clone();
        for s in 0..self.count() {
            let Some(t) = self.templates[s].clone() else {
                continue;
            };
            let pools: Vec<&[Ty]> = (0..=t.k).map(|_| base.as_slice()).collect();
            let mut cands = Vec::new();
            product(&pools, &mut Vec::new(), &mut |ps| {
                cands.push(Ty::Ref(s, ps.to_vec()))
            });
            for c in cands {
                if !self.samples(oracle, &c).is_empty() {
                    out.push(c);
                }
            }
        }
        out
    }

    fn spread(&self, items: &[V], n: usize) -> Vec<V> {
        if items.len() <= n {
            return items.to_vec();
        }
        (0..n)
            .map(|i| items[i * (items.len() - 1) / (n - 1).max(1)].clone())
            .collect()
    }

    /// Whether `v` is in ground type `t`.
    pub fn holds<L: Language<Value = V>>(&mut self, oracle: &mut Oracle<L>, v: &V, t: &Ty) -> bool {
        if let Some(b) = self.holds_memo.get(&(v.clone(), t.clone())) {
            return *b;
        }
        let b = match t {
            Ty::Var(_) => false,
            Ty::Base(s) => self.sort(oracle, v) == Some(*s),
            Ty::Ref(s, ps) => {
                self.sort(oracle, v) == Some(*s) && {
                    let tmpl = self.templates[*s]
                        .clone()
                        .expect("refined sorts have a template");
                    let (res, args) = ps.split_last().unwrap();
                    let arg_samples: Vec<Vec<V>> =
                        args.iter().map(|a| self.samples(oracle, a)).collect();
                    let refs: Vec<&[V]> = arg_samples.iter().map(|a| a.as_slice()).collect();
                    let mut envs = Vec::new();
                    product(&refs, &mut Vec::new(), &mut |xs| {
                        envs.push(Self::env(v, xs))
                    });
                    envs.into_iter().take(81).all(|env| {
                        let o = oracle.eval_in(&tmpl.term, &env);
                        self.in_e(oracle, &o, res)
                    })
                }
            }
        };
        self.holds_memo.insert((v.clone(), t.clone()), b);
        b
    }

    /// Whether an outcome is good for ground type `t`: a value of it, an
    /// allowed fault, or out of fuel.
    pub fn in_e<L: Language<Value = V>>(
        &mut self,
        oracle: &mut Oracle<L>,
        o: &Outcome<V>,
        t: &Ty,
    ) -> bool {
        match o {
            Outcome::Value(w) => self.holds(oracle, w, t),
            Outcome::Stuck { .. } => false,
            Outcome::Fault(_) | Outcome::Timeout => true,
        }
    }

    /// Members of ground type `t` from the pool, spread from smallest to
    /// largest.
    pub fn samples<L: Language<Value = V>>(&mut self, oracle: &mut Oracle<L>, t: &Ty) -> Vec<V> {
        if let Some(s) = self.samples_memo.get(t) {
            return s.clone();
        }
        let n = self.samples_per_type;
        let out = match t {
            Ty::Var(_) => Vec::new(),
            Ty::Base(s) => self.spread(&self.members[*s].clone(), n),
            Ty::Ref(s, _) => {
                let ms = self.members[*s].clone();
                let fit: Vec<V> = ms
                    .iter()
                    .filter(|m| self.holds(oracle, m, t))
                    .take(64)
                    .cloned()
                    .collect();
                self.diverse(oracle, &fit, n)
            }
        };
        self.samples_memo.insert(t.clone(), out.clone());
        out
    }

    /// What `v`'s eliminator gives on a few probe arguments, as sorts (or
    /// -1 stuck, -2 fault, -3 out of fuel, -4 unsorted): a cheap
    /// fingerprint of a refined value's behaviour.
    fn behaviour<L: Language<Value = V>>(&mut self, oracle: &mut Oracle<L>, v: &V) -> Vec<i64> {
        if let Some(b) = self.behaviour_memo.get(v) {
            return b.clone();
        }
        let mut out = Vec::new();
        if let Some(t) = self.sort(oracle, v).and_then(|s| self.templates[s].clone()) {
            let probes: Vec<Vec<V>> = self
                .contexts
                .iter()
                .filter(|c| c.con == t.elim && c.hole == t.hole)
                .map(|c| c.probes.clone())
                .take(12)
                .collect();
            for p in probes {
                let o = oracle.eval_in(&t.term, &Self::env(v, &p));
                out.push(match o {
                    Outcome::Value(w) => self.sort(oracle, &w).map_or(-4, |s| s as i64),
                    Outcome::Stuck { .. } => -1,
                    Outcome::Fault(_) => -2,
                    Outcome::Timeout => -3,
                });
            }
        }
        self.behaviour_memo.insert(v.clone(), out.clone());
        out
    }

    /// Up to `n` of `items` that behave differently (`behaviour`), round
    /// robin, smallest first. The
    /// identity and a constant function are both `T<num -> num>`, and a
    /// test of a rule needs both.
    fn diverse<L: Language<Value = V>>(
        &mut self,
        oracle: &mut Oracle<L>,
        items: &[V],
        n: usize,
    ) -> Vec<V> {
        let mut groups: Vec<(Vec<i64>, Vec<V>)> = Vec::new();
        for v in items {
            let sig = self.behaviour(oracle, v);
            match groups.iter_mut().find(|(s, _)| *s == sig) {
                Some((_, vs)) => vs.push(v.clone()),
                None => groups.push((sig, vec![v.clone()])),
            }
        }
        let mut out = Vec::new();
        for round in 0.. {
            let mut any = false;
            for (_, vs) in &groups {
                if let Some(v) = vs.get(round) {
                    any = true;
                    if out.len() < n {
                        out.push(v.clone());
                    }
                }
            }
            if !any || out.len() >= n {
                break;
            }
        }
        out
    }

    /// The ground types in the universe that `v` is in.
    pub fn types_of<L: Language<Value = V>>(
        &mut self,
        oracle: &mut Oracle<L>,
        v: &V,
    ) -> Vec<usize> {
        (0..self.universe.len())
            .filter(|&i| {
                let t = self.universe[i].clone();
                self.holds(oracle, v, &t)
            })
            .collect()
    }
}
