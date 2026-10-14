//! The type checker a rule set induces: algorithm W over the rules, with
//! the variable rule built in and overloaded rules tried in turn.

use crate::lang::{Atom, Con, Kind, Term};
use crate::types::{Schema, Ty, Unifier};

pub struct Checker {
    by_con: Vec<Vec<Schema>>,
    kinds: Vec<Kind>,
    /// Typings kept per node when overloads branch.
    pub cap: usize,
}

impl Checker {
    pub fn new(sig: &[Con], rules: &[Schema]) -> Self {
        let mut by_con = vec![Vec::new(); sig.len()];
        for r in rules {
            by_con[r.con].push(r.clone());
        }
        Checker {
            by_con,
            kinds: sig.iter().map(|c| c.kind).collect(),
            cap: 8,
        }
    }

    /// The types a closed term can be given, each with its variables
    /// unconstrained.
    pub fn types(&self, t: &Term) -> Vec<Ty> {
        let mut ctx = Vec::new();
        let mut out: Vec<Ty> = self
            .infer(Unifier::default(), &mut ctx, t)
            .into_iter()
            .map(|(u, ty)| u.resolve(&ty))
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// `ctx.last()` is `var(0)`'s type.
    fn infer(&self, u: Unifier, ctx: &mut Vec<Ty>, t: &Term) -> Vec<(Unifier, Ty)> {
        if self.kinds[t.con] == Kind::Var {
            let Atom::Int(i) = t.atom else {
                return Vec::new();
            };
            let i = i as usize;
            return if i < ctx.len() {
                vec![(u, ctx[ctx.len() - 1 - i].clone())]
            } else {
                Vec::new()
            };
        }
        let mut out = Vec::new();
        for rule in &self.by_con[t.con] {
            let mut u = u.clone();
            let r = u.instantiate(rule);
            let mut alts = vec![u];
            for (kid, prem) in t.kids.iter().zip(&r.kids) {
                let mut next = Vec::new();
                for ua in alts {
                    let depth = ctx.len();
                    ctx.extend(prem.bound.iter().rev().cloned());
                    for (mut ub, ty) in self.infer(ua, ctx, kid) {
                        if ub.unify(&ty, &prem.ty) {
                            next.push(ub);
                        }
                    }
                    ctx.truncate(depth);
                }
                next.truncate(self.cap);
                alts = next;
                if alts.is_empty() {
                    break;
                }
            }
            out.extend(alts.into_iter().map(|ua| (ua, r.res.clone())));
        }
        out.truncate(self.cap);
        out
    }
}
