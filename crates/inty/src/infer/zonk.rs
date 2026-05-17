//! Resolve a [`Type`] against a [`VarTable`].
//!
//! "Zonking" is the GHC term (Peyton Jones et al. 2007, "Practical Type
//! Inference for Arbitrary-Rank Types", JFP 17(1)) for the operation
//! that walks a type and replaces every unification variable with its
//! current resolution. It is the destructive-unification replacement
//! for `Type::apply_subst` (`crates/inty/src/types/subst.rs`).
//!
//! This is Step 1 of `docs/destructive-unification-plan.md`: introduce
//! `zonk` as a pure function over [`VarTable`], proven equivalent to
//! `Subst::apply_subst` by property tests, with no production call
//! sites changed. Steps 2+ flip the call sites over.
//!
//! ## Invariants
//!
//! - Skolems (`TVarName::Skolem(_)`) are never looked up — they're
//!   rigid by construction. The walk returns them unchanged.
//! - Flex variables (`TVarName::Flex(id)`) are chased to their
//!   equivalence-class root via [`VarTable::find`]. If the root is
//!   `Unbound`, the result is `Type::Var(Flex(root))` — the renaming
//!   is *not* observable to callers that compare types via the rules
//!   in `unify`, but it does change the displayed variable in pretty
//!   output. (Step 4 introduces a separate display-only canonicaliser
//!   at the boundary so the LSP's letter-stable output isn't
//!   affected.)
//! - The walk recurses on structural shape. It is depth-bounded by
//!   the existing `ApplySubstGuard` machinery (we reuse it so the
//!   "type too deep" diagnostic stays consistent).

use crate::types::subst::ApplySubstGuard;
use crate::types::{
    FieldEntry, ModuleType, PropName, QualType, RowTail, RowType, TVarId, TVarName, Type, TypePred,
    TypeScheme,
};

use super::var_table::{Resolution, VarTable};

/// Resolve `ty` against `table`, returning a fully-zonked copy.
///
/// "Fully-zonked" means: no flex variable in the result is also bound
/// (or linked to a bound) in `table`. Free flex variables (whose root
/// is `Unbound`) remain as `Type::Var(Flex(root))`.
///
/// Bounded by the per-thread depth cap shared with `Type::apply_subst`
/// (see `crates/inty/src/types/subst.rs`). Past the cap, returns
/// `Type::Error` and sets the overflow flag for the driver to surface.
///
/// ## Cycle handling
///
/// Inty's normal inference path converts equi-recursive bindings to
/// nominal `Type::Named` references in `var_bind` / `create_recursive
/// _type`, so a well-formed substitution never holds a cycle on
/// directly-bound variables. The zonk walker additionally carries a
/// per-call `visited` set of variable roots: if a recursive resolution
/// would re-enter a root we're already mid-expanding, we return
/// `Type::Var(Flex(root))` (the variable unchanged) rather than
/// looping. This is the infernu-`Decycle` discipline (port of
/// `src/Infernu/Decycle.hs`), used here as defence-in-depth so a
/// drift between the HashMap mirror and the Union-Find table — which
/// the destructive-unification migration may produce mid-flight —
/// degrades to a harmless un-resolved variable rather than a SIGSEGV.
pub fn zonk(table: &mut VarTable, ty: &Type) -> Type {
    let mut visited: std::collections::HashSet<TVarId> = std::collections::HashSet::new();
    zonk_with_visited(table, ty, &mut visited)
}

fn zonk_with_visited(
    table: &mut VarTable,
    ty: &Type,
    visited: &mut std::collections::HashSet<TVarId>,
) -> Type {
    let Some(_guard) = ApplySubstGuard::try_enter() else {
        return Type::Error;
    };
    match ty {
        Type::Number => Type::Number,
        Type::String => Type::String,
        Type::Boolean => Type::Boolean,
        Type::Undefined => Type::Undefined,
        Type::Null => Type::Null,
        Type::Regex => Type::Regex,
        Type::Error => Type::Error,
        Type::Literal(lit) => Type::Literal(lit.clone()),
        Type::Var(TVarName::Skolem(_)) => ty.clone(),
        Type::Var(TVarName::Flex(id)) => {
            // Tolerant lookup: synthetic ids baked into builtin
            // stubs and test fixtures may sit outside the table's
            // dense `fresh()`-allocated range. Treat those as
            // unbound (the variable stays as-is) rather than
            // indexing out of bounds.
            let Some(root) = table.find_if_present(*id) else {
                return ty.clone();
            };
            // Decycle: if we're already mid-expanding `root`, return
            // the variable verbatim. A well-formed inty substitution
            // hits this only when zonk is called on a type that
            // *itself* loops through a malformed mirror entry; the
            // normal path goes through nominal `Type::Named`.
            if !visited.insert(root) {
                return Type::Var(TVarName::Flex(*id));
            }
            let result = match table.root_resolution(root) {
                // Free root: use the equivalence-class root id. This
                // mirrors `Subst::apply_subst`'s "follow the chain to
                // its endpoint" behaviour — for an aliased pair like
                // `unify(α, β)`, both zonk to the surviving root so
                // downstream `==` checks (the trampoline for unify
                // proper, occurs-check, etc.) treat them as equal.
                // It does mean unbound free variables may be displayed
                // under a different letter than the user wrote; the
                // pretty-printer's id-letter renumbering pass handles
                // that at the boundary.
                Resolution::Unbound { .. } => Type::Var(TVarName::Flex(root)),
                Resolution::Bound(bound) => {
                    let bound = bound.clone();
                    zonk_with_visited(table, &bound, visited)
                }
                Resolution::Link(_) => {
                    // `find` returned a root, so `root_resolution`
                    // can't yield Link. Defensive.
                    ty.clone()
                }
            };
            visited.remove(&root);
            result
        }
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type
                .as_ref()
                .map(|t| Box::new(zonk_with_visited(table, t, visited))),
            params: params
                .iter()
                .map(|p| zonk_with_visited(table, p, visited))
                .collect(),
            ret: Box::new(zonk_with_visited(table, ret, visited)),
        },
        Type::Row(row) => Type::Row(zonk_row_with_visited(table, row, visited)),
        Type::Array(elem) => Type::Array(Box::new(zonk_with_visited(table, elem, visited))),
        Type::Promise(inner) => {
            Type::Promise(Box::new(zonk_with_visited(table, inner, visited)))
        }
        Type::Map(value) => Type::Map(Box::new(zonk_with_visited(table, value, visited))),
        Type::Named(id, args) => Type::Named(
            *id,
            args.iter()
                .map(|a| zonk_with_visited(table, a, visited))
                .collect(),
        ),
        Type::Union(members) => Type::union(
            members
                .iter()
                .map(|m| zonk_with_visited(table, m, visited)),
        ),
        Type::Module(m) => Type::Module(ModuleType {
            source: m.source.clone(),
            exports: m
                .exports
                .iter()
                .map(|(k, scheme)| (k.clone(), zonk_scheme(table, scheme)))
                .collect(),
        }),
    }
}

/// Zonk a row type. Mirrors today's shallow row substitution: we
/// don't merge bound row-tail variables back into the prop map here
/// (that's `Subst::flatten`'s job at the boundary callers). This
/// keeps zonk-on-rows O(props), matching the cost target.
pub fn zonk_row(table: &mut VarTable, row: &RowType) -> RowType {
    let mut visited = std::collections::HashSet::new();
    zonk_row_with_visited(table, row, &mut visited)
}

fn zonk_row_with_visited(
    table: &mut VarTable,
    row: &RowType,
    visited: &mut std::collections::HashSet<TVarId>,
) -> RowType {
    let props: std::collections::BTreeMap<PropName, FieldEntry> = row
        .props
        .iter()
        .map(|(k, e)| {
            (
                k.clone(),
                FieldEntry {
                    presence: e.presence.clone(),
                    ty: zonk_with_visited(table, &e.ty, visited),
                },
            )
        })
        .collect();
    let tail = match &row.tail {
        RowTail::Closed => RowTail::Closed,
        RowTail::Open(TVarName::Skolem(_)) => row.tail.clone(),
        RowTail::Open(TVarName::Flex(id)) => {
            // Same tolerant lookup as the type-var case: synthetic
            // ids past the table's range stay as-is. Unbound roots
            // resolve to the Union-Find root id (matches
            // `Subst::apply_subst`'s chain-following endpoint).
            match table.find_if_present(*id) {
                None => row.tail.clone(),
                Some(root) => match table.root_resolution(root) {
                    Resolution::Unbound { .. } => RowTail::Open(TVarName::Flex(root)),
                    Resolution::Bound(_) => {
                        // Tail bound to a structured type — shallow zonk
                        // leaves the surface tail as the original variable
                        // (matches today's `RowType::apply_subst` shallow
                        // behaviour). The deep-merge case is the
                        // `Subst::flatten` path called at boundaries.
                        RowTail::Open(TVarName::Flex(*id))
                    }
                    Resolution::Link(_) => row.tail.clone(),
                },
            }
        }
        RowTail::Recursive(id, args) => RowTail::Recursive(
            *id,
            args.iter()
                .map(|a| zonk_with_visited(table, a, visited))
                .collect(),
        ),
    };
    RowType { props, tail }
}

/// Zonk a type predicate (the head of a type-class constraint).
pub fn zonk_pred(table: &mut VarTable, pred: &TypePred) -> TypePred {
    TypePred {
        class: pred.class.clone(),
        types: pred.types.iter().map(|t| zonk(table, t)).collect(),
    }
}

/// Zonk a qualified type.
pub fn zonk_qual(table: &mut VarTable, q: &QualType) -> QualType {
    QualType {
        preds: q.preds.iter().map(|p| zonk_pred(table, p)).collect(),
        ty: zonk(table, &q.ty),
    }
}

/// Zonk a type scheme. Quantified vars are *not* looked up in the
/// table (they shadow the outer scope) — mirrors how
/// `TypeScheme::apply_subst` filters out the quantified set.
pub fn zonk_scheme(table: &mut VarTable, scheme: &TypeScheme) -> TypeScheme {
    // Quantified flex vars must not be substituted; temporarily
    // mark them. We achieve this by checking `scheme.vars` membership
    // on each `Type::Var` lookup. The simplest way to do that without
    // threading the set through every recursive call is to walk the
    // body and rewrite the body, treating any `Flex(v)` whose name
    // is in `scheme.vars` as opaque.
    let body = QualType {
        preds: scheme
            .body
            .preds
            .iter()
            .map(|p| TypePred {
                class: p.class.clone(),
                types: p
                    .types
                    .iter()
                    .map(|t| zonk_filtered(table, t, &scheme.vars))
                    .collect(),
            })
            .collect(),
        ty: zonk_filtered(table, &scheme.body.ty, &scheme.vars),
    };
    TypeScheme {
        vars: scheme.vars.clone(),
        pvars: scheme.pvars.clone(),
        body,
    }
}

fn zonk_filtered(table: &mut VarTable, ty: &Type, quantified: &[TVarName]) -> Type {
    let Some(_guard) = ApplySubstGuard::try_enter() else {
        return Type::Error;
    };
    match ty {
        Type::Var(name) if quantified.contains(name) => Type::Var(name.clone()),
        Type::Var(TVarName::Flex(id)) => {
            match table.root_resolution(*id) {
                Resolution::Unbound { .. } => {
                    let root = table.find(*id);
                    let canonical = TVarName::Flex(root);
                    if quantified.contains(&canonical) {
                        Type::Var(canonical)
                    } else {
                        Type::Var(canonical)
                    }
                }
                Resolution::Bound(bound) => {
                    let bound = bound.clone();
                    zonk_filtered(table, &bound, quantified)
                }
                Resolution::Link(_) => ty.clone(),
            }
        }
        Type::Var(_) => ty.clone(), // Skolem
        Type::Number | Type::String | Type::Boolean | Type::Undefined | Type::Null
        | Type::Regex | Type::Error => ty.clone(),
        Type::Literal(lit) => Type::Literal(lit.clone()),
        Type::Func { this_type, params, ret } => Type::Func {
            this_type: this_type.as_ref().map(|t| Box::new(zonk_filtered(table, t, quantified))),
            params: params.iter().map(|p| zonk_filtered(table, p, quantified)).collect(),
            ret: Box::new(zonk_filtered(table, ret, quantified)),
        },
        Type::Row(row) => Type::Row(zonk_row_filtered(table, row, quantified)),
        Type::Array(elem) => Type::Array(Box::new(zonk_filtered(table, elem, quantified))),
        Type::Promise(inner) => Type::Promise(Box::new(zonk_filtered(table, inner, quantified))),
        Type::Map(value) => Type::Map(Box::new(zonk_filtered(table, value, quantified))),
        Type::Named(id, args) => Type::Named(
            *id,
            args.iter().map(|a| zonk_filtered(table, a, quantified)).collect(),
        ),
        Type::Union(members) => Type::union(
            members.iter().map(|m| zonk_filtered(table, m, quantified)),
        ),
        Type::Module(m) => Type::Module(ModuleType {
            source: m.source.clone(),
            // Don't recurse into inner schemes here: they have their
            // own quantifier set. Zonk them fresh.
            exports: m.exports.iter().map(|(k, s)| (k.clone(), zonk_scheme(table, s))).collect(),
        }),
    }
}

fn zonk_row_filtered(
    table: &mut VarTable,
    row: &RowType,
    quantified: &[TVarName],
) -> RowType {
    let props: std::collections::BTreeMap<PropName, FieldEntry> = row
        .props
        .iter()
        .map(|(k, e)| {
            (
                k.clone(),
                FieldEntry {
                    presence: e.presence.clone(),
                    ty: zonk_filtered(table, &e.ty, quantified),
                },
            )
        })
        .collect();
    let tail = match &row.tail {
        RowTail::Closed => RowTail::Closed,
        RowTail::Open(name) if quantified.contains(name) => RowTail::Open(name.clone()),
        RowTail::Open(TVarName::Flex(id)) => match table.root_resolution(*id) {
            Resolution::Unbound { .. } => {
                let root = table.find(*id);
                RowTail::Open(TVarName::Flex(root))
            }
            Resolution::Bound(_) | Resolution::Link(_) => {
                RowTail::Open(TVarName::Flex(*id))
            }
        },
        RowTail::Open(skolem) => RowTail::Open(skolem.clone()),
        RowTail::Recursive(id, args) => RowTail::Recursive(
            *id,
            args.iter().map(|a| zonk_filtered(table, a, quantified)).collect(),
        ),
    };
    RowType { props, tail }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Subst, Substitutable, TVarId};

    /// Build a `Subst` mirroring a `VarTable`. Insertion discipline:
    ///
    /// - If `find(id) != id` (id is a non-root in some equivalence
    ///   class), insert `(id, Var(root))`. `apply_subst` then chases
    ///   `id → Var(root)` and lands at the same place `zonk` does.
    /// - If `find(id) == id` and the root is `Bound(t)`, insert
    ///   `(id, t)`. Aliased members reach `t` via their `(id,
    ///   Var(root))` chain entry; the root reaches `t` directly.
    /// - If `find(id) == id` and the root is `Unbound`, no entry.
    ///   Both `apply_subst` and `zonk` return the variable unchanged.
    ///
    /// The key property `zonk_matches_apply_subst_on_random_workloads`
    /// pins is `zonk(table, t) == subst_from_table(&table).apply(t)`.
    fn subst_from_table(table: &mut VarTable) -> Subst {
        let mut s = Subst::empty();
        for id in 0..table.len() as TVarId {
            let root = table.find(id);
            if root != id {
                s.insert(TVarName::Flex(id), Type::Var(TVarName::Flex(root)));
            }
            if let Resolution::Bound(ty) = table.root_resolution(id) {
                s.insert(TVarName::Flex(root), ty.clone());
            }
        }
        s
    }

    /// Round-trip: a non-cyclic substitution lifted into a VarTable
    /// produces the same zonk as `apply_subst`.
    #[test]
    fn zonk_matches_apply_subst_for_primitive_binding() {
        let mut table = VarTable::new();
        let a = table.fresh();
        table.bind(a, Type::Number);
        let ty = Type::Var(TVarName::Flex(a));

        let zonked = zonk(&mut table, &ty);
        assert_eq!(zonked, Type::Number);

        // Same via apply_subst.
        let subst = subst_from_table(&mut table);
        assert_eq!(subst.apply(&ty), Type::Number);
    }

    /// Chain: α → β → γ → Number. Zonking α reaches Number through
    /// path compression.
    #[test]
    fn zonk_chases_chain() {
        let mut table = VarTable::new();
        let a = table.fresh();
        let b = table.fresh();
        let c = table.fresh();
        table.union(a, b);
        table.union(b, c);
        table.bind(a, Type::String);

        for id in [a, b, c] {
            let zonked = zonk(&mut table, &Type::Var(TVarName::Flex(id)));
            assert_eq!(zonked, Type::String);
        }
    }

    /// An unbound variable zonks to itself (via its root id).
    #[test]
    fn zonk_leaves_unbound_alone() {
        let mut table = VarTable::new();
        let a = table.fresh();
        let zonked = zonk(&mut table, &Type::Var(TVarName::Flex(a)));
        assert_eq!(zonked, Type::Var(TVarName::Flex(a)));
    }

    /// Skolems are never looked up — they're rigid.
    #[test]
    fn zonk_leaves_skolems_alone() {
        let mut table = VarTable::new();
        let skolem = Type::Var(TVarName::Skolem(42));
        let zonked = zonk(&mut table, &skolem);
        assert_eq!(zonked, skolem);
    }

    /// Structural recursion: a function type with a bound arg gets
    /// zonked at the leaves.
    #[test]
    fn zonk_recurses_into_func() {
        let mut table = VarTable::new();
        let a = table.fresh();
        table.bind(a, Type::Number);
        let ty = Type::simple_func(vec![Type::Var(TVarName::Flex(a))], Type::Var(TVarName::Flex(a)));
        let zonked = zonk(&mut table, &ty);
        assert_eq!(zonked, Type::simple_func(vec![Type::Number], Type::Number));
    }

    /// Arrays, Promises, Maps zonk their inner type.
    #[test]
    fn zonk_recurses_into_compound() {
        let mut table = VarTable::new();
        let a = table.fresh();
        table.bind(a, Type::Boolean);
        let arr = Type::Array(Box::new(Type::Var(TVarName::Flex(a))));
        assert_eq!(zonk(&mut table, &arr), Type::Array(Box::new(Type::Boolean)));
        let prom = Type::Promise(Box::new(Type::Var(TVarName::Flex(a))));
        assert_eq!(
            zonk(&mut table, &prom),
            Type::Promise(Box::new(Type::Boolean))
        );
        let m = Type::Map(Box::new(Type::Var(TVarName::Flex(a))));
        assert_eq!(zonk(&mut table, &m), Type::Map(Box::new(Type::Boolean)));
    }

    /// Bound chains through other binds: α → Number, β bound to
    /// `Array(α)`. Zonking `β` resolves both.
    #[test]
    fn zonk_resolves_through_binding_indirection() {
        let mut table = VarTable::new();
        let a = table.fresh();
        let b = table.fresh();
        table.bind(a, Type::Number);
        table.bind(b, Type::Array(Box::new(Type::Var(TVarName::Flex(a)))));

        let zonked = zonk(&mut table, &Type::Var(TVarName::Flex(b)));
        assert_eq!(zonked, Type::Array(Box::new(Type::Number)));
    }

    /// Property-style: build a sequence of fresh+bind ops and confirm
    /// `zonk(table, ty) == apply_subst(subst_from_table, ty)` for a
    /// set of probe types. Run for a handful of seeds; the existing
    /// proptest dev-dep is already in scope.
    #[test]
    fn zonk_matches_apply_subst_on_random_workloads() {
        use proptest::prelude::*;
        use proptest::strategy::ValueTree;
        let mut runner = proptest::test_runner::TestRunner::default();
        let strategy = proptest::collection::vec(any::<u8>(), 1..40);
        for _ in 0..32 {
            let bytes = strategy.new_tree(&mut runner).unwrap().current();
            let mut table = VarTable::new();
            // Generate `bytes.len()` fresh vars.
            let ids: Vec<TVarId> = (0..bytes.len()).map(|_| table.fresh()).collect();
            // For each byte, decide an action: 0..63 bind to primitive,
            // 64..127 union with previous, 128..255 leave free.
            for (i, &b) in bytes.iter().enumerate() {
                if b < 64 && i > 0 {
                    // Choose primitive deterministically.
                    let p = match b % 4 {
                        0 => Type::Number,
                        1 => Type::String,
                        2 => Type::Boolean,
                        _ => Type::Null,
                    };
                    // Skip if already bound (find returns root; if root
                    // is bound, second bind would panic).
                    let root = table.find(ids[i]);
                    if matches!(table.root_resolution(root), Resolution::Unbound { .. }) {
                        table.bind(ids[i], p);
                    }
                } else if b < 128 && i > 0 {
                    let j = (b as usize) % i;
                    let r1 = table.find(ids[i]);
                    let r2 = table.find(ids[j]);
                    if r1 != r2 {
                        // Only union if both roots still unbound.
                        if matches!(table.root_resolution(r1), Resolution::Unbound { .. })
                            && matches!(table.root_resolution(r2), Resolution::Unbound { .. })
                        {
                            table.union(ids[i], ids[j]);
                        }
                    }
                }
            }
            // Build the equivalent substitution.
            let subst = subst_from_table(&mut table);
            // Probe with a few synthesised types referencing the vars.
            for &id in &ids {
                let probe = Type::Var(TVarName::Flex(id));
                let z = zonk(&mut table, &probe);
                let s = subst.apply(&probe);
                assert_eq!(
                    z, s,
                    "zonk vs apply_subst mismatch on id={} (zonk={:?}, apply_subst={:?})",
                    id, z, s
                );
            }
            // Compound probe: function from id[0] -> Array(id[1]).
            if ids.len() >= 2 {
                let probe = Type::simple_func(
                    vec![Type::Var(TVarName::Flex(ids[0]))],
                    Type::Array(Box::new(Type::Var(TVarName::Flex(ids[1])))),
                );
                assert_eq!(zonk(&mut table, &probe), subst.apply(&probe));
            }
        }
    }

    /// Empty union zonk: passes through (it would be a malformed input
    /// since `Type::union` normalises to a single member when given one).
    #[test]
    fn zonk_union_normalises() {
        let mut table = VarTable::new();
        let a = table.fresh();
        table.bind(a, Type::Number);
        let probe = Type::union(vec![
            Type::Var(TVarName::Flex(a)),
            Type::String,
        ]);
        let zonked = zonk(&mut table, &probe);
        let expected = Type::union(vec![Type::Number, Type::String]);
        assert_eq!(zonked, expected);
    }
}
