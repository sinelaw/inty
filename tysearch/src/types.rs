//! Types, typing-rule schemas, and the operations the search and the
//! checker need on them: matching, unification and generalisation.
//!
//! A type is a discovered sort, a refined sort, or a variable. A refined
//! sort `T3<A -> R>` is the values of sort `T3` that, given to `T3`'s
//! eliminator with other arguments of types `A`, give an `R`: when the
//! eliminator is application, that is a function type (`semantics`).

use std::collections::HashMap;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Ty {
    Var(u32),
    Base(usize),
    /// A refined sort: its eliminator's other arguments' types, then the
    /// result's.
    Ref(usize, Vec<Ty>),
    /// Every value: inty's `unknown`, the type of what a `catch` binds.
    /// Nothing can be done with one but what can be done with anything.
    Top,
    /// No value: the exit type where there is nothing to return from.
    Never,
}

impl Ty {
    pub fn vars(&self, out: &mut Vec<u32>) {
        match self {
            Ty::Var(v) => {
                if !out.contains(v) {
                    out.push(*v)
                }
            }
            Ty::Base(_) | Ty::Top | Ty::Never => {}
            Ty::Ref(_, ps) => ps.iter().for_each(|p| p.vars(out)),
        }
    }

    pub fn is_ground(&self) -> bool {
        match self {
            Ty::Var(_) => false,
            Ty::Base(_) | Ty::Top | Ty::Never => true,
            Ty::Ref(_, ps) => ps.iter().all(Ty::is_ground),
        }
    }

    /// Sort constants: how much the type commits to.
    pub fn constants(&self) -> usize {
        match self {
            Ty::Var(_) => 0,
            Ty::Base(_) | Ty::Top | Ty::Never => 1,
            Ty::Ref(_, ps) => 1 + ps.iter().map(Ty::constants).sum::<usize>(),
        }
    }

    pub fn depth(&self) -> usize {
        match self {
            Ty::Ref(_, ps) => 1 + ps.iter().map(Ty::depth).max().unwrap_or(0),
            _ => 0,
        }
    }

    fn map_vars(&self, f: &mut impl FnMut(u32) -> Ty) -> Ty {
        match self {
            Ty::Var(v) => f(*v),
            Ty::Base(s) => Ty::Base(*s),
            Ty::Top => Ty::Top,
            Ty::Never => Ty::Never,
            Ty::Ref(s, ps) => Ty::Ref(*s, ps.iter().map(|p| p.map_vars(f)).collect()),
        }
    }
}

/// A child's premise: the types of the variables it sees bound (`var(0)`
/// first), its own type, and, if not the node's, its exit type: what a
/// `return` in it may carry (a function's body's is the function's
/// result).
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Premise {
    pub bound: Vec<Ty>,
    pub ty: Ty,
    pub exit: Option<Ty>,
}

/// A typing rule for constructor `con`:
///
/// ```text
///   Γ, bound₁ ⊢ e₁ : P₁  …  Γ, boundₙ ⊢ eₙ : Pₙ
///   ───────────────────────────────────────────
///          Γ ⊢ con(e₁, …, eₙ) : P₀
/// ```
///
/// Every judgement has an exit type besides (what a `return` in the term
/// may carry), the node's passed down to each child unless its premise
/// says otherwise; `exit`, if the rule fixes the node's (`return e` needs
/// it to be `e`'s type).
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Schema {
    pub con: usize,
    pub kids: Vec<Premise>,
    pub res: Ty,
    pub exit: Option<Ty>,
}

impl Schema {
    /// Every type in the rule, premises first.
    pub fn types(&self) -> impl Iterator<Item = &Ty> {
        self.kids
            .iter()
            .flat_map(|k| k.bound.iter().chain([&k.ty]).chain(&k.exit))
            .chain([&self.res])
            .chain(&self.exit)
    }

    /// Whether the rule says anything about exit types.
    pub fn has_exits(&self) -> bool {
        self.exit.is_some() || self.kids.iter().any(|k| k.exit.is_some())
    }

    pub fn vars(&self) -> Vec<u32> {
        let mut out = Vec::new();
        self.types().for_each(|t| t.vars(&mut out));
        out
    }

    pub fn constants(&self) -> usize {
        self.types().map(Ty::constants).sum()
    }

    /// Whether the result's variables all occur in a premise: otherwise the
    /// rule claims a type it has no evidence for.
    pub fn res_bound(&self) -> bool {
        let mut prem = Vec::new();
        for k in &self.kids {
            k.bound
                .iter()
                .chain([&k.ty])
                .for_each(|t| t.vars(&mut prem));
        }
        let mut res = Vec::new();
        self.res.vars(&mut res);
        res.iter().all(|v| prem.contains(v))
    }

    pub fn map_vars(&self, f: &mut impl FnMut(u32) -> Ty) -> Schema {
        Schema {
            con: self.con,
            kids: self
                .kids
                .iter()
                .map(|k| Premise {
                    bound: k.bound.iter().map(|t| t.map_vars(f)).collect(),
                    ty: k.ty.map_vars(f),
                    exit: k.exit.as_ref().map(|t| t.map_vars(f)),
                })
                .collect(),
            res: self.res.map_vars(f),
            exit: self.exit.as_ref().map(|t| t.map_vars(f)),
        }
    }

    /// Variables renumbered by first appearance, so rules equal up to
    /// renaming are equal.
    pub fn normalize(&self) -> Schema {
        let order = self.vars();
        self.map_vars(&mut |v| Ty::Var(order.iter().position(|w| *w == v).unwrap() as u32))
    }
}

/// Matches pattern `p` against ground `g`, extending `theta`.
pub fn match_ground(p: &Ty, g: &Ty, theta: &mut HashMap<u32, Ty>) -> bool {
    match (p, g) {
        (Ty::Var(v), _) => match theta.get(v) {
            Some(b) => b == g,
            None => {
                theta.insert(*v, g.clone());
                true
            }
        },
        (Ty::Base(a), Ty::Base(b)) => a == b,
        (Ty::Top, Ty::Top) | (Ty::Never, Ty::Never) => true,
        (Ty::Ref(a, ps), Ty::Ref(b, gs)) => {
            a == b
                && ps.len() == gs.len()
                && ps.iter().zip(gs).all(|(p, g)| match_ground(p, g, theta))
        }
        _ => false,
    }
}

pub fn subst(t: &Ty, theta: &HashMap<u32, Ty>) -> Ty {
    t.map_vars(&mut |v| theta.get(&v).cloned().unwrap_or(Ty::Var(v)))
}

/// A substitution for unification, with fresh variables.
#[derive(Clone, Default, Debug)]
pub struct Unifier {
    map: HashMap<u32, Ty>,
    pub next: u32,
}

impl Unifier {
    pub fn fresh(&mut self) -> Ty {
        self.next += 1;
        Ty::Var(self.next - 1)
    }

    /// A copy of `s` with fresh variables.
    pub fn instantiate(&mut self, s: &Schema) -> Schema {
        let mut m: HashMap<u32, Ty> = HashMap::new();
        s.map_vars(&mut |v| m.entry(v).or_insert_with(|| self.fresh()).clone())
    }

    pub fn resolve(&self, t: &Ty) -> Ty {
        match t {
            Ty::Var(v) => match self.map.get(v) {
                Some(b) => self.resolve(b),
                None => t.clone(),
            },
            Ty::Base(_) | Ty::Top | Ty::Never => t.clone(),
            Ty::Ref(s, ps) => Ty::Ref(*s, ps.iter().map(|p| self.resolve(p)).collect()),
        }
    }

    fn occurs(&self, v: u32, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(w) => v == w,
            Ty::Base(_) | Ty::Top | Ty::Never => false,
            Ty::Ref(_, ps) => ps.iter().any(|p| self.occurs(v, p)),
        }
    }

    pub fn unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let (a, b) = (self.shallow(a), self.shallow(b));
        match (&a, &b) {
            (Ty::Var(x), Ty::Var(y)) if x == y => true,
            (Ty::Var(x), t) | (t, Ty::Var(x)) => {
                if self.occurs(*x, t) {
                    return false;
                }
                self.map.insert(*x, t.clone());
                true
            }
            (Ty::Base(x), Ty::Base(y)) => x == y,
            (Ty::Top, Ty::Top) | (Ty::Never, Ty::Never) => true,
            (Ty::Ref(x, ps), Ty::Ref(y, qs)) => {
                x == y && ps.len() == qs.len() && ps.iter().zip(qs).all(|(p, q)| self.unify(p, q))
            }
            _ => false,
        }
    }

    /// What `t` stands for, one variable deep: the last variable on its
    /// chain (if any) and that variable's binding, or `t` itself.
    pub fn binding(&self, t: &Ty) -> (Option<u32>, Ty) {
        let mut last = None;
        let mut cur = t.clone();
        while let Ty::Var(v) = cur {
            match self.map.get(&v) {
                Some(b) => {
                    last = Some(v);
                    cur = b.clone();
                }
                None => return (last, Ty::Var(v)),
            }
        }
        (last, cur)
    }

    /// Changes a bound variable's binding.
    pub fn rebind(&mut self, v: u32, t: Ty) {
        self.map.insert(v, t);
    }

    fn shallow(&self, t: &Ty) -> Ty {
        match t {
            Ty::Var(v) => match self.map.get(v) {
                Some(b) => self.shallow(b),
                None => t.clone(),
            },
            _ => t.clone(),
        }
    }
}

/// Plotkin's least general generalisation of rules of one shape: the most
/// specific rule they are all instances of, and for each of its new
/// variables the types it stands for in each rule. `+ : (T0, T0) -> T0`
/// and `+ : (T1, T1) -> T1` give `+ : (a, a) -> a` with `a` for `T0` and
/// `T1`: read as a type class. Of ground instances observed together, it
/// is the candidate rule they suggest (as in Golem's relative lgg).
pub fn lgg(rules: &[Schema]) -> Option<(Schema, Vec<Vec<Ty>>)> {
    let shape = |s: &Schema| {
        (
            s.kids
                .iter()
                .map(|k| (k.bound.len(), k.exit.is_some()))
                .collect::<Vec<_>>(),
            s.exit.is_some(),
        )
    };
    if rules.is_empty()
        || rules
            .iter()
            .any(|r| shape(r) != shape(&rules[0]) || r.con != rules[0].con)
    {
        return None;
    }
    let mut columns: Vec<Vec<Ty>> = Vec::new();
    let offset = rules
        .iter()
        .map(|r| r.vars().len() as u32)
        .max()
        .unwrap_or(0);
    let positions: Vec<Vec<Ty>> = rules.iter().map(|r| r.types().cloned().collect()).collect();
    let mut it = (0..positions[0].len())
        .map(|i| {
            let col: Vec<Ty> = positions.iter().map(|p| p[i].clone()).collect();
            au(&col, &mut columns, offset)
        })
        .collect::<Vec<_>>()
        .into_iter();
    let schema = Schema {
        con: rules[0].con,
        kids: rules[0]
            .kids
            .iter()
            .map(|k| Premise {
                bound: k.bound.iter().map(|_| it.next().unwrap()).collect(),
                ty: it.next().unwrap(),
                exit: k.exit.as_ref().map(|_| it.next().unwrap()),
            })
            .collect(),
        res: it.next().unwrap(),
        exit: rules[0].exit.as_ref().map(|_| it.next().unwrap()),
    };
    Some((schema, columns))
}

fn au(col: &[Ty], columns: &mut Vec<Vec<Ty>>, offset: u32) -> Ty {
    if col.iter().all(|t| *t == col[0]) {
        return col[0].clone();
    }
    if let Ty::Ref(s, ps) = &col[0] {
        if col
            .iter()
            .all(|t| matches!(t, Ty::Ref(s2, ps2) if s2 == s && ps2.len() == ps.len()))
        {
            let args = (0..ps.len())
                .map(|j| {
                    let sub: Vec<Ty> = col
                        .iter()
                        .map(|t| match t {
                            Ty::Ref(_, ps) => ps[j].clone(),
                            _ => unreachable!(),
                        })
                        .collect();
                    au(&sub, columns, offset)
                })
                .collect();
            return Ty::Ref(*s, args);
        }
    }
    let v = columns.iter().position(|c| c == col).unwrap_or_else(|| {
        columns.push(col.to_vec());
        columns.len() - 1
    });
    Ty::Var(offset + v as u32)
}

/// Names for printing: the sorts', and `a`, `b`, … for variables.
pub struct Names<'a> {
    pub sorts: &'a [String],
    pub cons: &'a [&'a str],
    /// Per refined sort, its eliminators' names and parameter counts.
    pub shapes: &'a [Vec<(String, usize)>],
}

impl Names<'_> {
    pub fn ty(&self, t: &Ty) -> String {
        match t {
            Ty::Var(v) => var_name(*v),
            Ty::Base(s) => self.sorts[*s].clone(),
            Ty::Top => "unknown".into(),
            Ty::Never => "never".into(),
            Ty::Ref(s, ps) => {
                let shape = self.shapes.get(*s).map_or(&[][..], |v| v.as_slice());
                let slice = |ps: &[Ty]| {
                    let (res, args) = ps.split_last().unwrap();
                    let args: Vec<String> = args.iter().map(|a| self.ty(a)).collect();
                    format!("{} -> {}", args.join(", "), self.ty(res))
                };
                if shape.len() <= 1 {
                    format!("{}<{}>", self.sorts[*s], slice(ps))
                } else {
                    // One part per eliminator: `T2{fst: -> a, snd: -> b}`.
                    let mut at = 0;
                    let parts: Vec<String> = shape
                        .iter()
                        .map(|(name, n)| {
                            at += n;
                            format!("{name}: {}", slice(&ps[at - n..at]).trim_start())
                        })
                        .collect();
                    format!("{}{{{}}}", self.sorts[*s], parts.join(", "))
                }
            }
        }
    }

    pub fn schema(&self, s: &Schema) -> String {
        let kids: Vec<String> = s
            .kids
            .iter()
            .map(|k| {
                let ty = match &k.exit {
                    Some(e) => format!("{} (return {})", self.ty(&k.ty), self.ty(e)),
                    None => self.ty(&k.ty),
                };
                if k.bound.is_empty() {
                    ty
                } else {
                    let b: Vec<String> = k
                        .bound
                        .iter()
                        .enumerate()
                        .map(|(i, t)| format!("x{i}: {}", self.ty(t)))
                        .collect();
                    format!("[{}] {ty}", b.join(", "))
                }
            })
            .collect();
        let con = self.cons[s.con];
        let res = match &s.exit {
            Some(e) => format!("{} (return {})", self.ty(&s.res), self.ty(e)),
            None => self.ty(&s.res),
        };
        if kids.is_empty() {
            format!("{con} : {res}")
        } else {
            format!("{con} : ({}) -> {res}", kids.join(", "))
        }
    }
}

pub fn var_name(v: u32) -> String {
    if v < 26 {
        ((b'a' + v as u8) as char).to_string()
    } else {
        format!("t{v}")
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
