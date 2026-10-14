//! Every term up to a size: the small-scope corpus that observation and
//! the end-to-end check both draw from.

use crate::lang::{Con, Term};

/// All closed terms of size at most `max`, smallest first.
pub fn terms_up_to(sig: &[Con], max: usize) -> Vec<Term> {
    let mut by_size: Vec<Vec<Term>> = vec![Vec::new(); max + 1];
    for size in 1..=max {
        let mut out = Vec::new();
        for (ci, c) in sig.iter().enumerate() {
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
                let pools: Vec<&[Term]> = split.iter().map(|&s| by_size[s].as_slice()).collect();
                product(&pools, &mut Vec::new(), &mut |kids| {
                    out.push(Term::new(ci, kids.to_vec()))
                });
            }
        }
        by_size[size] = out;
    }
    by_size.concat()
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

/// Calls `f` on each choice of one term from each pool.
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
