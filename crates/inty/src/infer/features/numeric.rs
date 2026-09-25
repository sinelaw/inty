//! `Int` and `Number`: the numeric classes and their solver.
//!
//! `Int` is the refinement of `Number` with no fractional part. Three
//! classes relate them:
//!
//! * `Num a` — `a` is `Int` or `Number`. What an arithmetic operand must be.
//! * `NumLit a` — the same, for the type of an integral literal. It only
//!   differs in defaulting: to `Int`, where a `Num` defaults to `Number`.
//!   So `let i = 0; xs[i]` indexes with an `Int` and `let t = 0; t += 0.5`
//!   makes `t` a `Number` — the literal's type waits for its uses.
//! * `Arith a b c` — `c` is the type of `a ∘ b` for `+ - * %`: `Int` when
//!   both are `Int`, `Number` when either is. A lub, not an equation, so
//!   `i * 0.5` doesn't make `i` a `Number`.
//!
//! `Arith`'s improvement rules (all sound: they follow from `c = a ⊔ b`):
//! `a` and `b` known → `c`; either `Number` → `c = Number`; `c = Int` →
//! `a = b = Int`; `c = Number` and one side `Int` → the other `Number`.
//!
//! Numeric variables nothing else determines are *defaulted* where a
//! scheme is generalised and at the end of inference (Haskell's
//! defaulting): a literal's to `Int`, any other to `Number`. That keeps
//! `function inc(x) { return x + 1; }` at `(Number) => Number` rather
//! than a scheme over `Arith`. A variable some other constraint determines
//! — an index (`a[i + 1]`, fixed by the container), a property read, the
//! environment — is left alone, and so is everything connected to it by
//! `Arith`: defaulting one would constrain the others.

use std::collections::HashSet;

use crate::error::IntyError;
use crate::span::Span;
use crate::types::{ClassName, LitValue, TVarName, Type, TypePred};

use super::super::state::InferState;
use super::super::InferResult;

/// What a type says about a numeric slot.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum NumKind {
    Int,
    Number,
    /// A variable (or anything else not yet a number type).
    Unknown,
}

fn is_integral(n: f64) -> bool {
    crate::types::is_safe_int(n)
}

impl InferState {
    /// `widen_fresh_literals`, except that an integral number literal
    /// widens to a fresh `NumLit` variable — `Int` or `Number`, as its
    /// uses decide — instead of to `Number`.
    pub(crate) fn widen(&mut self, span: Span, ty: &Type) -> Type {
        let mut fresh = Vec::new();
        let widened = ty.widen_fresh_literals_with(&mut |lit| match lit {
            LitValue::Number(n) if is_integral(*n) => {
                let v = self.fresh_type_var();
                fresh.push(v.clone());
                v
            }
            other => other.base_type(),
        });
        for v in fresh {
            self.add_constraint(TypePred::num_lit(v), span);
        }
        widened
    }

    /// The numeric kind of `ty`, as far as it's known now.
    pub(crate) fn num_kind(&mut self, ty: &Type) -> NumKind {
        match self.zonk(ty) {
            Type::Int => NumKind::Int,
            Type::Number => NumKind::Number,
            Type::Literal(LitValue::Number(n)) if is_integral(n) => NumKind::Int,
            Type::Literal(LitValue::Number(_)) => NumKind::Number,
            _ => NumKind::Unknown,
        }
    }

    /// Whether `ty` is a number type, a number literal, or a
    /// number-kinded variable (see `InferState::numeric_vars`).
    pub(crate) fn is_numeric(&mut self, ty: &Type) -> bool {
        let ty = self.zonk(ty);
        match &ty {
            Type::Int | Type::Number | Type::Literal(LitValue::Number(_)) => true,
            Type::Var(v @ TVarName::Flex(_)) => self.numeric_vars.contains(v),
            _ => false,
        }
    }

    /// `Num ty`: checked now for a known type (with the message a
    /// `Number` slot would give), posed for a variable.
    pub(crate) fn require_num(&mut self, span: Span, ty: &Type) -> InferResult<()> {
        match self.zonk(ty) {
            Type::Int | Type::Number | Type::Literal(LitValue::Number(_)) | Type::Error => Ok(()),
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::num(ty.clone()), span);
                Ok(())
            }
            _ => self.subsume(span, ty, &Type::Number),
        }
    }

    /// The type of `left ∘ right` for `+ - * %` on numbers. Operands are
    /// already widened.
    pub(crate) fn arith(&mut self, span: Span, left: &Type, right: &Type) -> InferResult<Type> {
        self.require_num(span, left)?;
        self.require_num(span, right)?;
        match (self.num_kind(left), self.num_kind(right)) {
            (NumKind::Int, NumKind::Int) => Ok(Type::Int),
            (NumKind::Number, _) | (_, NumKind::Number) => Ok(Type::Number),
            _ => {
                let result = self.fresh_type_var();
                self.add_constraint(TypePred::num(result.clone()), span);
                self.add_constraint(
                    TypePred::arith(left.clone(), right.clone(), result.clone()),
                    span,
                );
                Ok(result)
            }
        }
    }

    /// The least number type of two known ones, for a join.
    pub(crate) fn numeric_lub(&mut self, t1: &Type, t2: &Type) -> Option<Type> {
        match (self.num_kind(t1), self.num_kind(t2)) {
            (NumKind::Int, NumKind::Number) | (NumKind::Number, NumKind::Int) => Some(Type::Number),
            _ => None,
        }
    }

    /// Resolve `Num`/`NumLit`: a number type holds, a variable waits,
    /// anything else fails.
    pub(crate) fn resolve_num(&mut self, ty: &Type, span: Span) -> Result<(), IntyError> {
        match self.zonk(ty) {
            Type::Int | Type::Number | Type::Literal(LitValue::Number(_)) | Type::Error => Ok(()),
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::num(ty.clone()), span);
                Ok(())
            }
            other => Err(self.unification_error(span, &Type::Number, &other)),
        }
    }

    /// Apply `Arith a b c`'s improvement rules; re-pose it if they don't
    /// decide it yet.
    pub(crate) fn resolve_arith(
        &mut self,
        a: &Type,
        b: &Type,
        c: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        let (ka, kb, kc) = (self.num_kind(a), self.num_kind(b), self.num_kind(c));
        use NumKind::*;
        match (ka, kb, kc) {
            (_, _, Int) => {
                self.unify_num(span, a, Type::Int)?;
                self.unify_num(span, b, Type::Int)
            }
            (Number, _, _) | (_, Number, _) => self.unify_num(span, c, Type::Number),
            (Int, Int, _) => self.unify_num(span, c, Type::Int),
            // `Int` is the least number type: `Int ⊔ b = b`. (`b` is still
            // a number: re-posed, since this constraint said so.)
            (Int, Unknown, _) => {
                self.unify(span, c, b)?;
                self.resolve_num(b, span)
            }
            (Unknown, Int, _) => {
                self.unify(span, c, a)?;
                self.resolve_num(a, span)
            }
            // `a ⊔ a = a`.
            _ if self.zonk(a) == self.zonk(b) => {
                self.unify(span, c, a)?;
                self.resolve_num(a, span)
            }
            _ => {
                self.add_constraint(TypePred::arith(a.clone(), b.clone(), c.clone()), span);
                Ok(())
            }
        }
    }

    /// Bind a numeric slot: a literal already there only has to fit.
    fn unify_num(&mut self, span: Span, slot: &Type, ty: Type) -> Result<(), IntyError> {
        match self.zonk(slot) {
            lit @ Type::Literal(_) => self.subsume(span, &lit, &ty),
            _ => self.unify(span, slot, &ty),
        }
    }

    /// Resolve the numeric constraints the improvement rules decide,
    /// repeatedly (one can decide another).
    pub(crate) fn simplify_numeric(&mut self) -> Result<(), IntyError> {
        if !self
            .pending_constraints
            .iter()
            .any(|c| is_numeric_class(c.pred.class))
        {
            return Ok(());
        }
        loop {
            let before: Vec<TypePred> = self
                .pending_constraints
                .iter()
                .filter(|c| is_numeric_class(c.pred.class))
                .map(|c| self.apply_subst_pred(&c.pred))
                .collect();
            let all = std::mem::take(&mut self.pending_constraints);
            let (numeric, rest): (Vec<_>, Vec<_>) = all
                .into_iter()
                .partition(|c| is_numeric_class(c.pred.class));
            self.pending_constraints = rest;
            for c in numeric {
                self.resolve_numeric_pred(&c.pred, c.span)?;
            }
            let after: Vec<TypePred> = self
                .pending_constraints
                .iter()
                .filter(|c| is_numeric_class(c.pred.class))
                .map(|c| self.apply_subst_pred(&c.pred))
                .collect();
            if after == before {
                return Ok(());
            }
        }
    }

    fn resolve_numeric_pred(&mut self, pred: &TypePred, span: Span) -> Result<(), IntyError> {
        match pred.class {
            ClassName::Num => self.resolve_num(&pred.types[0], span),
            ClassName::NumLit => match self.zonk(&pred.types[0]) {
                // Still undecided: keep the literal's default.
                v @ Type::Var(TVarName::Flex(_)) => {
                    self.add_constraint(TypePred::num_lit(v), span);
                    Ok(())
                }
                _ => self.resolve_num(&pred.types[0], span),
            },
            ClassName::Arith => {
                let (a, b, c) = (
                    pred.types[0].clone(),
                    pred.types[1].clone(),
                    pred.types[2].clone(),
                );
                self.resolve_arith(&a, &b, &c, span)
            }
            _ => unreachable!("resolve_numeric_pred: not a numeric class"),
        }
    }

    /// Default the numeric variables whose choice is free, and simplify
    /// the constraints the choice doesn't matter to (see the module docs).
    ///
    /// With `ty`, where a scheme for `ty` is about to be generalised
    /// (`fixed` being what the environment holds): a variable `ty` doesn't
    /// mention is *ambiguous* and defaults — to `Int` for a literal's, to
    /// `Number` otherwise, both always valid; a variable only in parameter
    /// position whose value no result depends on becomes `Number` (a caller
    /// may still pass an `Int`: `Int ≤ Number` at the argument); one only
    /// in result position that no constraint determines becomes `Int` (a
    /// caller may still use it as a `Number`). What's left relates inputs
    /// to outputs and stays polymorphic: `x => x * 2` is
    /// `<a> where Num a => (a) => a`.
    ///
    /// Without `ty` — the end of the program — every variable defaults
    /// (operands before results, which then follow). With `force`, even
    /// those another constraint determines. Returns whether anything was
    /// defaulted.
    pub(crate) fn default_numeric(
        &mut self,
        fixed: &HashSet<TVarName>,
        ty: Option<&Type>,
        force: bool,
    ) -> Result<bool, IntyError> {
        self.simplify_numeric()?;
        let mut defaulted_any = false;
        loop {
            // (Recomputed each round: defaulting and improvement merge
            // variables.)
            let polarity = ty.map(|t| {
                let t = self.main_subst.flatten(t);
                let t = self.zonk(&t);
                let mut out = std::collections::HashMap::new();
                collect_polarity(&t, POS, &mut out);
                out
            });
            let preds: Vec<TypePred> = self
                .pending_constraints
                .iter()
                .map(|c| self.apply_subst_pred(&c.pred))
                .collect();
            let var_of = |t: &Type| match t {
                Type::Var(v @ TVarName::Flex(_)) => Some(v.clone()),
                _ => None,
            };
            // Variables another constraint determines.
            let mut blocked: HashSet<TVarName> = fixed.clone();
            if !force {
                for p in &preds {
                    let determined: &[Type] = match p.class {
                        ClassName::HasProp => p.types.get(2..).unwrap_or(&[]),
                        ClassName::Indexable => &p.types[1..],
                        _ => &[],
                    };
                    for t in determined {
                        blocked.extend(t.free_vars());
                    }
                }
            }
            let directly_blocked = blocked.clone();
            // Components connected by `Arith`: blocked as a whole.
            let numeric: Vec<&TypePred> =
                preds.iter().filter(|p| is_numeric_class(p.class)).collect();
            let ariths: Vec<(Type, Type, Type)> = numeric
                .iter()
                .filter(|p| p.class == ClassName::Arith)
                .map(|p| (p.types[0].clone(), p.types[1].clone(), p.types[2].clone()))
                .collect();
            let mut changed = true;
            while changed {
                changed = false;
                for p in &numeric {
                    let vars: Vec<TVarName> = p.types.iter().filter_map(var_of).collect();
                    if vars.iter().any(|v| blocked.contains(v))
                        && vars.iter().any(|v| !blocked.contains(v))
                    {
                        blocked.extend(vars);
                        changed = true;
                    }
                }
            }
            let results: HashSet<TVarName> =
                ariths.iter().filter_map(|(_, _, c)| var_of(c)).collect();
            let literal: HashSet<TVarName> = numeric
                .iter()
                .filter(|p| p.class == ClassName::NumLit)
                .filter_map(|p| var_of(&p.types[0]))
                .collect();
            // A literal operand is the exception: `a ⊔ Int = a`, so its
            // default constrains nothing else in its component.
            let free_literal = |v: &TVarName| {
                literal.contains(v) && !results.contains(v) && !directly_blocked.contains(v)
            };
            let candidates: Vec<TVarName> = {
                let mut seen = HashSet::new();
                let mut vs = Vec::new();
                for p in &numeric {
                    for v in p.types.iter().filter_map(var_of) {
                        if (!blocked.contains(&v) || free_literal(&v)) && seen.insert(v.clone()) {
                            vs.push(v);
                        }
                    }
                }
                vs.sort_by_key(|v| v.id());
                vs
            };
            let default_for = |v: &TVarName| {
                if literal.contains(v) {
                    Type::Int
                } else {
                    Type::Number
                }
            };
            let pick: Option<(TVarName, Type)> = match &polarity {
                None => candidates
                    .iter()
                    .find(|v| !results.contains(v))
                    .or_else(|| candidates.first())
                    .map(|v| (v.clone(), default_for(v))),
                Some(polarity) => {
                    // Variables a result (or anything else `ty` mentions)
                    // depends on through `Arith`: operand → result edges,
                    // walked backwards from the mentioned ones.
                    let mut feeds: HashSet<TVarName> = polarity
                        .iter()
                        .filter(|(_, f)| **f & (POS | INV) != 0)
                        .map(|(v, _)| v.clone())
                        .collect();
                    let mut grew = true;
                    while grew {
                        grew = false;
                        for (a, b, c) in &ariths {
                            if var_of(c).is_some_and(|c| feeds.contains(&c)) {
                                for v in [a, b].into_iter().filter_map(var_of) {
                                    grew |= feeds.insert(v);
                                }
                            }
                        }
                    }
                    candidates.iter().find_map(|v| {
                        let flags = polarity.get(v).copied().unwrap_or(0);
                        if blocked.contains(v) {
                            // (A free literal: see above.)
                            (flags == 0).then(|| (v.clone(), Type::Int))
                        } else if flags == 0 {
                            // Ambiguous: an operand's choice is free (the
                            // result it feeds follows); a result's is not.
                            (!results.contains(v)).then(|| (v.clone(), default_for(v)))
                        } else if flags == NEG && !feeds.contains(v) {
                            Some((v.clone(), Type::Number))
                        } else if flags == POS && !results.contains(v) {
                            Some((v.clone(), Type::Int))
                        } else {
                            None
                        }
                    })
                }
            };
            let Some((v, default)) = pick else {
                if polarity.is_some() && self.drop_unused_ariths(&blocked, polarity.as_ref())? {
                    continue;
                }
                return Ok(defaulted_any);
            };
            self.unify(Span::default(), &Type::Var(v), &default)?;
            defaulted_any = true;
            self.simplify_numeric()?;
        }
    }

    /// Drop `Arith a b c` for a `c` nothing uses — not the type, no other
    /// constraint: some `c` always exists (`a ⊔ b`), so it only says `a`
    /// and `b` are numbers, which their own `Num`s already say.
    fn drop_unused_ariths(
        &mut self,
        blocked: &HashSet<TVarName>,
        polarity: Option<&std::collections::HashMap<TVarName, u8>>,
    ) -> Result<bool, IntyError> {
        let preds: Vec<TypePred> = self
            .pending_constraints
            .iter()
            .map(|c| self.apply_subst_pred(&c.pred))
            .collect();
        let mentioned = |v: &TVarName| polarity.is_some_and(|p| p.contains_key(v));
        for (i, p) in preds.iter().enumerate() {
            if p.class != ClassName::Arith {
                continue;
            }
            let Type::Var(c @ TVarName::Flex(_)) = &p.types[2] else {
                continue;
            };
            if blocked.contains(c) || mentioned(c) {
                continue;
            }
            let used_elsewhere = preds.iter().enumerate().any(|(j, q)| {
                j != i
                    && !matches!(q.class, ClassName::Num | ClassName::NumLit)
                    && q.types.iter().any(|t| t.free_vars().contains(c))
            });
            if used_elsewhere || p.types[..2].iter().any(|t| t.free_vars().contains(c)) {
                continue;
            }
            let c = c.clone();
            let span = self.pending_constraints[i].span;
            self.pending_constraints.remove(i);
            for t in &p.types[..2] {
                self.require_num(span, t)?;
            }
            self.pending_constraints.retain(|k| {
                !(matches!(k.pred.class, ClassName::Num | ClassName::NumLit)
                    && k.pred.types[0] == Type::Var(c.clone()))
            });
            return Ok(true);
        }
        Ok(false)
    }
}

const POS: u8 = 1;
const NEG: u8 = 2;
const INV: u8 = 4;

/// Where each variable occurs in `ty`: as a result (`POS`), a parameter
/// (`NEG`), or somewhere neither subsumption direction applies (`INV` —
/// inside an array, an object, …: `Int ≤ Number` only holds for values).
fn collect_polarity(ty: &Type, pol: u8, out: &mut std::collections::HashMap<TVarName, u8>) {
    let flip = |p: u8| match p {
        POS => NEG,
        NEG => POS,
        other => other,
    };
    match ty {
        Type::Var(v @ TVarName::Flex(_)) => *out.entry(v.clone()).or_insert(0) |= pol,
        Type::Func {
            this_type,
            params,
            ret,
        } => {
            if let Some(t) = this_type {
                collect_polarity(t, INV, out);
            }
            for p in params {
                collect_polarity(&p.ty, flip(pol), out);
            }
            collect_polarity(ret, pol, out);
        }
        Type::Row(row) => {
            for (k, f) in &row.props {
                let p = if k.0 == crate::types::CALLABLE_KEY {
                    pol
                } else {
                    INV
                };
                collect_polarity(&f.ty, p, out);
            }
            if let crate::types::RowTail::Open(v) = &row.tail {
                *out.entry(v.clone()).or_insert(0) |= INV;
            }
        }
        Type::Union(ms) => {
            for m in ms {
                collect_polarity(m, pol, out);
            }
        }
        other => {
            for v in other.free_vars() {
                *out.entry(v).or_insert(0) |= INV;
            }
        }
    }
}

/// A scheme's predicates without the ones others imply: repeats, a `Num`
/// beside the `NumLit` on the same variable, a `Num` or `Plus` on a
/// variable an `Arith` already makes a number.
pub(crate) fn tidy_scheme_preds(preds: Vec<TypePred>) -> Vec<TypePred> {
    let in_arith: Vec<Type> = preds
        .iter()
        .filter(|p| p.class == ClassName::Arith)
        .flat_map(|p| p.types.iter().cloned())
        .collect();
    let lit: Vec<Type> = preds
        .iter()
        .filter(|p| p.class == ClassName::NumLit)
        .map(|p| p.types[0].clone())
        .collect();
    let numeric: Vec<Type> = preds
        .iter()
        .filter(|p| is_numeric_class(p.class))
        .flat_map(|p| p.types.iter().cloned())
        .collect();
    let mut out: Vec<TypePred> = Vec::new();
    for p in preds {
        let t = p.types.first();
        let implied = match p.class {
            ClassName::Num => t.is_some_and(|t| in_arith.contains(t) || lit.contains(t)),
            ClassName::NumLit => t.is_some_and(|t| in_arith.contains(t)),
            ClassName::Plus => t.is_some_and(|t| numeric.contains(t)),
            _ => false,
        };
        if !implied && !out.contains(&p) {
            out.push(p);
        }
    }
    out
}

pub(crate) fn is_numeric_class(class: ClassName) -> bool {
    matches!(class, ClassName::Num | ClassName::NumLit | ClassName::Arith)
}
