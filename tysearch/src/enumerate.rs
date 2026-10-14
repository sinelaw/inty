//! Every term up to a size, and a few at random beyond it.

use crate::lang::{Atom, Con, Kind, Term};

/// All terms of size at most `max` whose free variables are below `depth`,
/// smallest first.
pub fn terms_up_to(sig: &[Con], max: usize, depth: usize) -> Vec<Term> {
    Enumerator::new(sig, max).up_to(max, depth)
}

/// Terms by size and scope depth, built bottom up and memoised.
pub struct Enumerator<'a> {
    sig: &'a [Con],
    /// `memo[depth][size]`, filled on demand.
    memo: Vec<Vec<Option<Vec<Term>>>>,
    max: usize,
    /// Stop growing a size class past this many terms.
    pub cap: usize,
}

impl<'a> Enumerator<'a> {
    pub fn new(sig: &'a [Con], max: usize) -> Self {
        Enumerator {
            sig,
            memo: Vec::new(),
            max,
            cap: usize::MAX,
        }
    }

    pub fn up_to(&mut self, max: usize, depth: usize) -> Vec<Term> {
        (1..=max.min(self.max))
            .flat_map(|s| self.exactly(s, depth).to_vec())
            .collect()
    }

    pub fn exactly(&mut self, size: usize, depth: usize) -> &[Term] {
        while self.memo.len() <= depth {
            self.memo.push(vec![None; self.max + 1]);
        }
        if self.memo[depth][size].is_none() {
            let terms = self.build(size, depth);
            self.memo[depth][size] = Some(terms);
        }
        self.memo[depth][size].as_deref().unwrap()
    }

    fn build(&mut self, size: usize, depth: usize) -> Vec<Term> {
        let mut out = Vec::new();
        let sig = self.sig;
        let cap = self.cap;
        for (ci, c) in sig.iter().enumerate() {
            if c.kind == Kind::Var {
                if size == 1 {
                    out.extend((0..depth).map(|i| Term::leaf(ci, Atom::Int(i as i64))));
                }
                continue;
            }
            if c.arity == 0 {
                if size == 1 {
                    out.extend(c.atoms_or_none().into_iter().map(|a| Term::leaf(ci, a)));
                }
                continue;
            }
            if size < 1 + c.arity {
                continue;
            }
            for split in compositions(size - 1, c.arity) {
                let pools: Vec<Vec<Term>> = split
                    .iter()
                    .zip(&c.binds)
                    .map(|(&s, &b)| self.exactly(s, depth + b).to_vec())
                    .collect();
                let refs: Vec<&[Term]> = pools.iter().map(|p| p.as_slice()).collect();
                for atom in c.atoms_or_none() {
                    product(&refs, &mut Vec::new(), &mut |kids| {
                        if out.len() < cap {
                            out.push(Term {
                                con: ci,
                                atom: atom.clone(),
                                kids: kids.to_vec(),
                            })
                        }
                    });
                }
            }
        }
        out
    }
}

/// The ways to write `n` as `parts` positive summands, in order.
fn compositions(n: usize, parts: usize) -> Vec<Vec<usize>> {
    if parts == 1 {
        return if n >= 1 { vec![vec![n]] } else { Vec::new() };
    }
    let mut out = Vec::new();
    for first in 1..n {
        for mut rest in compositions(n - first, parts - 1) {
            rest.insert(0, first);
            out.push(rest);
        }
    }
    out
}

/// Calls `f` on each choice of one item from each pool.
pub fn product<T: Clone>(pools: &[&[T]], acc: &mut Vec<T>, f: &mut impl FnMut(&[T])) {
    if acc.len() == pools.len() {
        f(acc);
        return;
    }
    for t in pools[acc.len()] {
        acc.push(t.clone());
        product(pools, acc, f);
        acc.pop();
    }
}

/// A small deterministic generator (SplitMix64), so runs are repeatable.
pub struct Rng(pub u64);

impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n.max(1) as u64) as usize
    }

    /// Up to `n` items of `items`, spread over it, in order.
    pub fn sample<T: Clone>(&mut self, items: &[T], n: usize) -> Vec<T> {
        if items.len() <= n {
            return items.to_vec();
        }
        let mut idx: Vec<usize> = (0..n).map(|_| self.below(items.len())).collect();
        idx.sort();
        idx.dedup();
        idx.into_iter().map(|i| items[i].clone()).collect()
    }
}
