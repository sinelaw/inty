//! The type checker a rule set induces: algorithm W over the rules, with
//! the variable rule built in and overloaded rules tried in turn.

use crate::lang::{Atom, Con, Kind, Term};
use crate::types::{Schema, Ty, Unifier};

/// The subtype order on sorts, and joins.
#[derive(Clone, Debug)]
pub struct Order {
    pub le: Vec<Vec<bool>>,
    pub join: Vec<Vec<Option<usize>>>,
}

pub struct Checker {
    by_con: Vec<Vec<Schema>>,
    kinds: Vec<Kind>,
    /// With subtyping, the order on sorts and their joins: a child may
    /// have a subtype of its premise's type, and a variable fixed at a
    /// sort widens to the join when a later child needs it.
    pub order: Option<Order>,
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
            order: None,
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

    /// Whether a child of type `ty` meets premise `prem`: by unification,
    /// or with subtyping, by subsumption between sorts.
    fn fits(&self, u: &mut Unifier, ty: &Ty, prem: &Ty) -> bool {
        let Some(order) = &self.order else {
            return u.unify(ty, prem);
        };
        let Ty::Base(a) = u.resolve(ty) else {
            return u.unify(ty, prem);
        };
        match u.binding(prem) {
            // A sort in the rule itself.
            (None, Ty::Base(b)) => order.le[a][b],
            // A variable already fixed at a sort: fine if below it, else
            // widened to the join. The children typed against it so far
            // stay below the join, and the result only grows.
            (Some(v), Ty::Base(b)) => {
                if order.le[a][b] {
                    true
                } else if let Some(j) = order.join[a][b] {
                    u.rebind(v, Ty::Base(j));
                    true
                } else {
                    false
                }
            }
            _ => u.unify(ty, prem),
        }
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
                        if self.fits(&mut ub, &ty, &prem.ty) {
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
