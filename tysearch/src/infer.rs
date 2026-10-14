//! The type checker a rule set induces: algorithm W over the rules, with
//! the variable and assignment rules built in, overloaded rules tried in
//! turn, and let-polymorphism where a binder's policy allows it. And its
//! dual, `generate`: random programs well typed by construction, to run
//! (the test tier T2 of DESIGN.md).

use crate::enumerate::Rng;
use crate::lang::{Atom, Con, Kind, Term};
use crate::types::{Schema, Ty, Unifier};
use std::collections::HashMap;

/// The subtype order on sorts, and joins.
#[derive(Clone, Debug)]
pub struct Order {
    pub le: Vec<Vec<bool>>,
    pub join: Vec<Vec<Option<usize>>>,
}

/// When a bound variable, whose value is a child's, gets that child's type
/// generalised: never; when the child is a syntactic value (Wright's value
/// restriction); or always. A generalisable variable may also be used
/// monomorphically; only a monomorphic one may be assigned.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Policy {
    Never,
    IfValue,
    Always,
}

/// A type scheme in the context: `ty` with `quant` bound.
#[derive(Clone, Debug)]
struct Sch {
    quant: Vec<u32>,
    ty: Ty,
}

pub struct Checker {
    by_con: Vec<Vec<Schema>>,
    sig: Vec<Con>,
    /// With subtyping, the order on sorts and their joins: a child may
    /// have a subtype of its premise's type, and a variable fixed at a
    /// sort widens to the join when a later child needs it.
    pub order: Option<Order>,
    /// Per bound variable `(con, child, index)` whose value is child `k`'s:
    /// its policy, and `k`.
    pub policies: HashMap<(usize, usize, usize), (Policy, usize)>,
    /// Constructors whose terms are syntactic values: they run none of
    /// their children (literals, functions).
    pub inert: Vec<bool>,
    /// Typings kept per node when overloads branch.
    pub cap: usize,
    /// How much likelier `generate` picks a generalised variable than any
    /// other choice: what exercises a generalisation policy.
    pub poly_weight: usize,
    /// Likewise for an assignment: state is what breaks generalisation.
    pub assign_weight: usize,
}

impl Checker {
    pub fn new(sig: &[Con], rules: &[Schema]) -> Self {
        let mut by_con = vec![Vec::new(); sig.len()];
        for r in rules {
            by_con[r.con].push(r.clone());
        }
        Checker {
            by_con,
            sig: sig.to_vec(),
            order: None,
            policies: HashMap::new(),
            inert: vec![false; sig.len()],
            cap: 8,
            poly_weight: 4,
            assign_weight: 1,
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

    /// The schemes bound variable `j` of child `i` of `t` may get: its type
    /// as is, and generalised where the policy allows.
    fn schemes(&self, u: &Unifier, ctx: &[Sch], t: &Term, i: usize, j: usize, ty: &Ty) -> Vec<Sch> {
        let mono = Sch {
            quant: Vec::new(),
            ty: ty.clone(),
        };
        let Some(&(policy, k)) = self.policies.get(&(t.con, i, j)) else {
            return vec![mono];
        };
        let allowed = match policy {
            Policy::Never => false,
            Policy::IfValue => t.kids.get(k).is_some_and(|kid| self.inert[kid.con]),
            Policy::Always => true,
        };
        if !allowed {
            return vec![mono];
        }
        let ty = u.resolve(ty);
        let mut free = Vec::new();
        for s in ctx {
            let mut vs = Vec::new();
            u.resolve(&s.ty).vars(&mut vs);
            free.extend(vs.into_iter().filter(|v| !s.quant.contains(v)));
        }
        let mut quant = Vec::new();
        ty.vars(&mut quant);
        quant.retain(|v| !free.contains(v));
        if quant.is_empty() {
            return vec![mono];
        }
        vec![Sch { quant, ty }, mono]
    }

    fn instantiate(u: &mut Unifier, s: &Sch) -> Ty {
        let m: HashMap<u32, Ty> = s.quant.iter().map(|&v| (v, u.fresh())).collect();
        crate::types::subst(&s.ty, &m)
    }

    fn lookup(ctx: &[Sch], i: &Atom) -> Option<Sch> {
        match i {
            Atom::Int(i) if (*i as usize) < ctx.len() => {
                Some(ctx[ctx.len() - 1 - *i as usize].clone())
            }
            _ => None,
        }
    }

    /// `ctx.last()` is `var(0)`'s scheme.
    fn infer(&self, u: Unifier, ctx: &mut Vec<Sch>, t: &Term) -> Vec<(Unifier, Ty)> {
        match self.sig[t.con].kind {
            Kind::Var => {
                let Some(s) = Self::lookup(ctx, &t.atom) else {
                    return Vec::new();
                };
                let mut u = u;
                let ty = Self::instantiate(&mut u, &s);
                vec![(u, ty)]
            }
            Kind::Assign => {
                let Some(s) = Self::lookup(ctx, &t.atom).filter(|s| s.quant.is_empty()) else {
                    return Vec::new();
                };
                self.infer(u, ctx, &t.kids[0])
                    .into_iter()
                    .filter_map(|(mut u, ty)| {
                        self.fits(&mut u, &ty, &s.ty).then_some((u, s.ty.clone()))
                    })
                    .collect()
            }
            Kind::Op => {
                let mut out = Vec::new();
                for rule in &self.by_con[t.con] {
                    let mut u = u.clone();
                    let r = u.instantiate(rule);
                    let mut alts = vec![u];
                    for (i, (kid, prem)) in t.kids.iter().zip(&r.kids).enumerate() {
                        let mut next = Vec::new();
                        for ua in alts {
                            // Each way of typing the bound variables.
                            let mut binds: Vec<Vec<Sch>> = vec![Vec::new()];
                            for (j, b) in prem.bound.iter().enumerate() {
                                let options = self.schemes(&ua, ctx, t, i, j, b);
                                binds = binds
                                    .into_iter()
                                    .flat_map(|bs| {
                                        options.iter().map(move |o| {
                                            let mut bs = bs.clone();
                                            bs.push(o.clone());
                                            bs
                                        })
                                    })
                                    .collect();
                            }
                            for bs in binds {
                                let depth = ctx.len();
                                ctx.extend(bs.into_iter().rev());
                                for (mut ub, ty) in self.infer(ua.clone(), ctx, kid) {
                                    if self.fits(&mut ub, &ty, &prem.ty) {
                                        next.push(ub);
                                    }
                                }
                                ctx.truncate(depth);
                            }
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
    }

    /// A random closed term of at most `size` nodes, well typed by
    /// construction: built top down from the rules, each choice unified
    /// with what it must be, backtracking a little on failure.
    pub fn generate(&self, rng: &mut Rng, size: usize) -> Option<Term> {
        self.generate_shaped(rng, size, &[])
    }

    /// As `generate`, the constructors along the path of last children
    /// restricted: `shape[d]` says which may stand at depth `d` (say, a
    /// `let` whose body is a function).
    pub fn generate_shaped(&self, rng: &mut Rng, size: usize, shape: &[Vec<bool>]) -> Option<Term> {
        let mut u = Unifier::default();
        let want = u.fresh();
        let t = self.gen(rng, &mut u, &mut Vec::new(), &want, size, &mut 64, shape)?;
        // Generation can type a term in ways inference won't find (an
        // overload branch past the cap): keep only what the checker types.
        (!self.types(&t).is_empty()).then_some(t)
    }

    fn gen(
        &self,
        rng: &mut Rng,
        u: &mut Unifier,
        ctx: &mut Vec<Sch>,
        want: &Ty,
        size: usize,
        fuel: &mut usize,
        shape: &[Vec<bool>],
    ) -> Option<Term> {
        let here = shape.first();
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        enum Choice {
            Var(usize),
            Assign(usize),
            Rule(usize),
        }
        // The choices that fit `want`, each tried on a copy first.
        let mut choices = Vec::new();
        let rules: Vec<&Schema> = self.by_con.iter().flatten().collect();
        for i in 0..ctx.len() {
            if here.is_some() {
                break;
            }
            let s = &ctx[ctx.len() - 1 - i];
            let mut u2 = u.clone();
            let ty = Self::instantiate(&mut u2, s);
            if u2.unify(&ty, want) {
                choices.push(Choice::Var(i));
                // Variables are leaves: likelier when there's little room;
                // and a generalised one, used at another type, is what
                // tells a policy apart from a stricter one.
                if size <= 2 {
                    choices.push(Choice::Var(i));
                }
                if !s.quant.is_empty() {
                    for _ in 0..self.poly_weight {
                        choices.push(Choice::Var(i));
                    }
                }
                if size >= 2 && s.quant.is_empty() {
                    for _ in 0..self.assign_weight {
                        choices.push(Choice::Assign(i));
                    }
                }
            }
        }
        for (ri, r) in rules.iter().enumerate() {
            if r.kids.len() + 1 > size || here.is_some_and(|h| !h[r.con]) {
                continue;
            }
            let mut u2 = u.clone();
            let inst = u2.instantiate(r);
            if u2.unify(&inst.res, want) {
                choices.push(Choice::Rule(ri));
            }
        }
        for _ in 0..3 {
            if choices.is_empty() {
                return None;
            }
            let pick = choices.swap_remove(rng.below(choices.len()));
            let mut u2 = u.clone();
            let built = match pick {
                Choice::Var(i) => {
                    let ty = Self::instantiate(&mut u2, &ctx[ctx.len() - 1 - i]);
                    u2.unify(&ty, want);
                    let var = self.sig.iter().position(|c| c.kind == Kind::Var)?;
                    Some(Term::leaf(var, Atom::Int(i as i64)))
                }
                Choice::Assign(i) => {
                    let ty = ctx[ctx.len() - 1 - i].ty.clone();
                    u2.unify(&ty, want);
                    let con = self.sig.iter().position(|c| c.kind == Kind::Assign)?;
                    self.gen(rng, &mut u2, ctx, &ty, size - 1, fuel, &[])
                        .map(|e| Term {
                            con,
                            atom: Atom::Int(i as i64),
                            kids: vec![e],
                        })
                }
                Choice::Rule(ri) => self.gen_rule(
                    rng,
                    &mut u2,
                    ctx,
                    rules[ri],
                    want,
                    size,
                    fuel,
                    shape.get(1..).unwrap_or(&[]),
                ),
            };
            if let Some(t) = built {
                *u = u2;
                return Some(t);
            }
        }
        None
    }

    #[allow(clippy::too_many_arguments)]
    fn gen_rule(
        &self,
        rng: &mut Rng,
        u: &mut Unifier,
        ctx: &mut Vec<Sch>,
        rule: &Schema,
        want: &Ty,
        size: usize,
        fuel: &mut usize,
        shape: &[Vec<bool>],
    ) -> Option<Term> {
        let r = u.instantiate(rule);
        if !u.unify(&r.res, want) {
            return None;
        }
        let c = &self.sig[rule.con];
        let atoms = c.atoms_or_none();
        let atom = atoms[rng.below(atoms.len())].clone();
        // Split what's left among the children, each at least 1.
        let n = r.kids.len();
        let mut budget = size - 1;
        let mut sizes = Vec::new();
        for i in 0..n {
            let rest = n - i - 1;
            let mine = 1 + rng.below(budget - rest);
            budget -= mine;
            sizes.push(mine);
        }
        let mut node = Term {
            con: rule.con,
            atom,
            kids: Vec::new(),
        };
        for (i, prem) in r.kids.iter().enumerate() {
            let mut bs = Vec::new();
            for (j, b) in prem.bound.iter().enumerate() {
                // Generalise where the policy allows, mostly.
                let options = self.schemes(u, ctx, &node, i, j, b);
                let pick = if rng.below(4) == 0 {
                    options.len() - 1
                } else {
                    0
                };
                bs.push(options[pick].clone());
            }
            let depth = ctx.len();
            ctx.extend(bs.into_iter().rev());
            // The shape goes on down the last child.
            let rest: &[Vec<bool>] = if i + 1 == n { shape } else { &[] };
            let kid = self.gen(rng, u, ctx, &prem.ty, sizes[i], fuel, rest);
            ctx.truncate(depth);
            node.kids.push(kid?);
        }
        Some(node)
    }
}
