//! Unification algorithm for type inference.
//!
//! Implements unification for types including:
//! - Basic types (primitives, functions, arrays)
//! - Row types with row polymorphism
//! - Recursive type detection and creation

use std::collections::BTreeMap;

use crate::error::{IntyError, TypeError};
use crate::span::Span;
use crate::types::{
    FieldEntry, PropName, RowTail, RowType, Subst, TVarId, TVarName, Type, TypeDef,
};

use super::state::{InferState, UnfoldAssumption};

/// Result type for unification.
pub type UnifyResult<T> = Result<T, IntyError>;

impl InferState {
    /// Unify two types, updating the substitution.
    ///
    /// The two operands are resolved through the Union-Find variable
    /// table (`crate::infer::zonk`) before structural matching.
    /// This is the destructive-unification half of Step 2 in
    /// `docs/destructive-unification-plan.md`: `zonk` uses
    /// path-compressing `find` rather than HashMap chain-chasing,
    /// so a chain `α → β → γ → T` collapses to a single hop on the
    /// first lookup. The HashMap mirror (`main_subst`) is kept in
    /// sync at every binding by `mirror_extend`; this site is the
    /// first read to migrate. `zonk` carries a visited-set
    /// (`infernu/Decycle.hs` discipline) so any structural cycle in
    /// the mirror degrades to a free variable rather than a SIGSEGV.
    pub fn unify(&mut self, span: Span, t1: &Type, t2: &Type) -> UnifyResult<()> {
        let t1 = super::zonk::zonk(&mut self.var_table, &self.main_subst, t1);
        let t2 = super::zonk::zonk(&mut self.var_table, &self.main_subst, t2);
        self.unify_impl(span, &t1, &t2)
    }

    fn unify_impl(&mut self, span: Span, t1: &Type, t2: &Type) -> UnifyResult<()> {
        match (t1, t2) {
            // Error sentinel absorbs anything. A binding whose
            // inference failed gets `Type::Error`; we don't want
            // *every* downstream use site to also fail. Unifying
            // `Error` with anything succeeds silently — no
            // substitution emitted, no constraint added.
            // The original error has already been reported by the
            // recovery point; cascading is the noise we're avoiding.
            (Type::Error, _) | (_, Type::Error) => Ok(()),

            // Same variable
            (Type::Var(v1), Type::Var(v2)) if v1 == v2 => Ok(()),

            // Flex variable binds to anything
            (Type::Var(TVarName::Flex(n)), t) | (t, Type::Var(TVarName::Flex(n))) => {
                self.var_bind(span, *n, t)
            }

            // Literal types unify with themselves only. The directed
            // `Lit ≤ Base` rule lives in `subsume` (S-LitBase) — see
            // `state.rs`. Putting it here would make `unify`
            // accept the unsound reverse direction `Base ≤ Lit`,
            // which lets `String` flow into a position expecting a
            // singleton like `"circle"` and breaks discriminated-
            // union narrowing.
            (Type::Literal(l1), Type::Literal(l2)) => {
                if l1 == l2 {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Union ~ Union: if both sides are equal as sets (we already
            // normalise), accept. Otherwise reject — the calling site
            // should use join() if it wants subsumption-style behaviour.
            (Type::Union(m1), Type::Union(m2)) => {
                if m1.len() == m2.len() && m1.iter().all(|t| m2.contains(t)) {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Union ~ T: succeed if T is a member of the union (after
            // subst). This is the bridge that lets `var x: T | undefined
            // = expr` accept an `expr` that infers as `T` or `undefined`.
            //
            // Only the *sound* `Lit ≤ Base` direction is honoured here:
            // a literal value `other` can sit where a `Base` member is
            // expected. The reverse — a `Base` value where a literal
            // member is expected — is unsound (not every `String` is
            // `"circle"`) and is intentionally rejected. Callers that
            // legitimately need that direction (e.g. discriminated
            // unions matched by row arms) go through `subsume`'s
            // S-UnionR rule, which structurally distributes the
            // value over the arms.
            (Type::Union(members), other) | (other, Type::Union(members)) => {
                let mut matched = false;
                for m in members {
                    let m = self.zonk(m);
                    if &m == other {
                        matched = true;
                        break;
                    }
                    // Literal-into-base subsumption: a literal value
                    // can be supplied where the union has a base
                    // member.
                    if let Type::Literal(lit) = other {
                        if m == lit.base_type() {
                            matched = true;
                            break;
                        }
                    }
                }
                if matched {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Skolems must match exactly
            (Type::Var(TVarName::Skolem(n1)), Type::Var(TVarName::Skolem(n2))) if n1 == n2 => {
                Ok(())
            }

            // Primitives
            (Type::Number, Type::Number) => Ok(()),
            (Type::String, Type::String) => Ok(()),
            (Type::Boolean, Type::Boolean) => Ok(()),
            (Type::Undefined, Type::Undefined) => Ok(()),
            (Type::Null, Type::Null) => Ok(()),
            (Type::Regex, Type::Regex) => Ok(()),

            // Functions
            (
                Type::Func {
                    this_type: this1,
                    params: params1,
                    ret: ret1,
                },
                Type::Func {
                    this_type: this2,
                    params: params2,
                    ret: ret2,
                },
            ) => {
                // Unify this types:
                // - None means "static function, doesn't use this"
                // - Static functions are compatible with any this type
                match (this1, this2) {
                    (None, None) => {} // Both static, nothing to unify
                    (None, Some(_)) | (Some(_), None) => {
                        // One is static - compatible with any this
                    }
                    (Some(t1), Some(t2)) => {
                        self.unify(span, t1, t2)?;
                    }
                }

                // Unify parameters position-wise. Per-param presence
                // (Shape B per the destructive-unification follow-up:
                // see Garrigue 1994 "Labeled and optional arguments
                // for OCaml") lets two functions with different
                // arities unify when the surplus positions are
                // marked Abs / presence-polymorphic. Walk both lists
                // up to the longer length; positions present on only
                // one side require that side's presence to unify
                // with Abs.
                let n = params1.len().max(params2.len());
                for i in 0..n {
                    match (params1.get(i), params2.get(i)) {
                        (Some(p1), Some(p2)) => {
                            self.unify_presence(span, &p1.presence, &p2.presence)?;
                            self.unify(span, &p1.ty, &p2.ty)?;
                        }
                        (Some(p1), None) => {
                            // Surplus formal on the left side: its
                            // presence must reduce to Abs for the
                            // shorter side to be callable here.
                            self.unify_presence(span, &p1.presence, &crate::types::Presence::Abs)?;
                        }
                        (None, Some(p2)) => {
                            self.unify_presence(span, &p2.presence, &crate::types::Presence::Abs)?;
                        }
                        (None, None) => unreachable!(),
                    }
                }

                // Unify return types
                self.unify(span, ret1, ret2)
            }

            // Row types
            (Type::Row(r1), Type::Row(r2)) => self.unify_rows(span, r1, r2),

            // Arrays
            (Type::Array(e1), Type::Array(e2)) => self.unify(span, e1, e2),

            // Array with row type - arrays have structural properties like `length`
            (Type::Array(elem), Type::Row(row)) | (Type::Row(row), Type::Array(elem)) => {
                self.unify_array_with_row(span, elem, row)
            }

            // Promises
            (Type::Promise(i1), Type::Promise(i2)) => self.unify(span, i1, i2),

            // Maps
            (Type::Map(v1), Type::Map(v2)) => self.unify(span, v1, v2),

            // Tuples — structural congruence: same arity, components
            // unified pairwise. A different arity is a distinct type and
            // falls through to the mismatch error below (no width
            // subtyping).
            (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
                for (x, y) in a.iter().zip(b.iter()) {
                    self.unify(span, x, y)?;
                }
                Ok(())
            }

            // Same named type (recursive or nominal): unify arguments
            // invariantly. For nominal types this is the *only* way they
            // unify — identical brand id, matching args.
            (Type::Named(id1, args1), Type::Named(id2, args2)) if id1 == id2 => {
                if args1.len() != args2.len() {
                    return Err(self.unification_error(span, t1, t2));
                }
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(span, a1, a2)?;
                }
                Ok(())
            }

            // Two named types with *different* ids. The two-Nominal case
            // is rejected up front (different brand identities never
            // interchange). For any case that involves an equirecursive
            // type — including (Nominal, Equirec), (Equirec, Nominal),
            // (Equirec, Equirec) — unrolling the equirecursive side and
            // recursing is sound. The coinductive assumption guards the
            // (Equirec, Equirec) sub-case against the alternating-unroll
            // infinite loop: two distinct recursive types of the same
            // shape would otherwise unroll forever (Brandt-Henglein
            // 1998; Pierce TAPL ch. 21).
            (Type::Named(id1, args1), Type::Named(id2, args2)) => {
                let n1 = self.is_nominal_type(*id1);
                let n2 = self.is_nominal_type(*id2);
                if n1 && n2 {
                    return Err(self.unification_error(span, t1, t2));
                }
                let assumption = UnfoldAssumption::NamedPair(
                    (*id1).min(*id2),
                    (*id1).max(*id2),
                );
                if self.unfold_assumptions.contains(&assumption) {
                    return Ok(());
                }
                self.unfold_assumptions.push(assumption);
                // Prefer unrolling the equirecursive side (definitionally
                // transparent); if both are equirecursive either works.
                let result = if !n1 {
                    match self.unroll_named(*id1, args1) {
                        Some(u) => self.unify(span, &u, t2),
                        None => Err(self.unification_error(span, t1, t2)),
                    }
                } else {
                    match self.unroll_named(*id2, args2) {
                        Some(u) => self.unify(span, t1, &u),
                        None => Err(self.unification_error(span, t1, t2)),
                    }
                };
                self.unfold_assumptions.pop();
                result
            }

            // Named vs anything else (a non-Named structural shape).
            (Type::Named(id, args), other) | (other, Type::Named(id, args)) => {
                if self.is_nominal_type(*id) {
                    // Nominal types have brand identity: they unify only
                    // with the same id (handled above), never by
                    // collapsing into a structurally-equivalent value
                    // — so `UserId` ≠ `Number`, and two distinct brands
                    // with identical shape stay distinct.
                    //
                    // One *bounded* exception: an **open-tailed row**
                    // constraint. Open rows with a flex tail are
                    // synthesized by inference (member-access
                    // fall-through in `rows.rs` posts
                    // `{prop: T | tail}` to demand a field on an
                    // un-resolved object), never authored by the user.
                    // When such a constraint flows back into a
                    // nominal-typed binding (the canonical case is a
                    // module-level `ROOT = Path(...)` whose use sites
                    // accumulated row constraints against the hoisted
                    // placeholder before the actual nominal type was
                    // bound; see `infer_stmt_list`'s hoisted-unify),
                    // unrolling and unifying lets the constraint resolve
                    // structurally against the instance row — exactly
                    // the transparency `infer_member_on_type` already
                    // gives at an immediate access site.
                    //
                    // A *closed* row is a concrete user-introduced value
                    // (object literal, fully-specified annotation), so
                    // it still fails — preserving nominal safety against
                    // structural duck-typing.
                    if let Type::Row(row) = other {
                        if matches!(row.tail, RowTail::Open(_)) {
                            let assumption = UnfoldAssumption::NamedRow(*id);
                            if self.unfold_assumptions.contains(&assumption) {
                                return Ok(());
                            }
                            if let Some(unrolled) = self.unroll_named(*id, args) {
                                self.unfold_assumptions.push(assumption);
                                let r = self.unify(span, &unrolled, other);
                                self.unfold_assumptions.pop();
                                return r;
                            }
                        }
                    }
                    Err(self.unification_error(span, t1, t2))
                } else if let Some(unrolled) = self.unroll_named(*id, args) {
                    // Equi-recursive type: unroll and unify structurally.
                    // Cycle-guarded so a recursive equi-type doesn't
                    // unroll forever against a row that mentions it.
                    let assumption = UnfoldAssumption::NamedRow(*id);
                    if self.unfold_assumptions.contains(&assumption) {
                        return Ok(());
                    }
                    self.unfold_assumptions.push(assumption);
                    let r = self.unify(span, &unrolled, other);
                    self.unfold_assumptions.pop();
                    r
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Modules are nominally identified by source path. Two
            // namespace-import bindings of the same file unify; two
            // bindings of different files don't, even if their export
            // shapes happen to coincide. This matches ES module identity:
            // each file is its own module.
            (Type::Module(m1), Type::Module(m2)) => {
                if m1.source == m2.source {
                    Ok(())
                } else {
                    Err(self.unification_error(span, t1, t2))
                }
            }

            // Mismatch
            _ => Err(self.unification_error(span, t1, t2)),
        }
    }

    /// Bind a type variable to a type (with occurs check).
    fn var_bind(&mut self, span: Span, var: TVarId, ty: &Type) -> UnifyResult<()> {
        // Don't bind to itself
        if let Type::Var(TVarName::Flex(id)) = ty {
            if *id == var {
                return Ok(());
            }
        }

        // Check if this would create a recursive type inside a row
        if self.is_inside_row_type(var, ty) {
            // Create a recursive type
            return self.create_recursive_type(span, var, ty);
        }

        // Standard occurs check
        if self.occurs_in(var, ty) {
            return Err(TypeError::OccursCheck {
                var: format!("t{}", var),
                ty: ty.to_string(),
                span,
            }
            .into());
        }

        // Bind the variable
        self.extend_subst(span, TVarName::Flex(var), ty.clone())
    }

    /// Unify an array type with a row type.
    /// Arrays have structural properties like `length: Number`.
    fn unify_array_with_row(&mut self, span: Span, elem: &Type, row: &RowType) -> UnifyResult<()> {
        // Check each property in the row against array's known properties
        for (prop_name, entry) in &row.props {
            match prop_name.0.as_str() {
                "length" => {
                    // Array.length is Number
                    self.unify(span, &entry.ty, &Type::Number)?;
                }
                _ => {
                    // Unknown property - arrays don't have arbitrary properties
                    return Err(TypeError::PropertyNotFound {
                        prop: prop_name.0.clone(),
                        obj_type: format!("{}[]", elem),
                        span,
                    }
                    .into());
                }
            }
        }

        // Handle the row tail
        match &row.tail {
            RowTail::Closed => {
                // Closed row with only known array properties - OK
                Ok(())
            }
            RowTail::Open(TVarName::Flex(id)) => {
                // Open row - bind the tail to a closed empty row
                // (arrays don't have additional arbitrary properties)
                self.extend_subst(
                    span,
                    TVarName::Flex(*id),
                    Type::Row(RowType::empty_closed()),
                )
            }
            RowTail::Open(TVarName::Skolem(_)) => {
                // Skolem tail can't be bound
                Err(self.unification_error(
                    span,
                    &Type::Array(Box::new(elem.clone())),
                    &Type::Row(row.clone()),
                ))
            }
            RowTail::Recursive(_, _) => {
                // Recursive tail doesn't make sense for arrays
                Err(self.unification_error(
                    span,
                    &Type::Array(Box::new(elem.clone())),
                    &Type::Row(row.clone()),
                ))
            }
        }
    }

    /// Unify two row types.
    fn unify_rows(&mut self, span: Span, r1: &RowType, r2: &RowType) -> UnifyResult<()> {
        // Collect all property names from both rows
        let mut all_props: Vec<PropName> =
            r1.props.keys().chain(r2.props.keys()).cloned().collect();
        all_props.sort();
        all_props.dedup();

        // Walk every prop that appears on either side. The Remy '94
        // judgment unifies fields pointwise on both presence and type:
        //
        //   present on both:  unify presences, unify types
        //   only on r1:       if r2 is closed -> r1's presence must be Abs
        //                     (so omitting it from a closed row is OK only
        //                     when r1 also says it's absent / pres-poly);
        //                     if r2 is open  -> the field flows into r2's
        //                     tail with its current presence.
        //   only on r2:       symmetric.
        for prop in &all_props {
            match (r1.props.get(prop), r2.props.get(prop)) {
                (Some(e1), Some(e2)) => {
                    self.unify_presence(span, &e1.presence, &e2.presence)?;
                    self.unify(span, &e1.ty, &e2.ty)?;
                }
                (Some(e1), None) => match &r2.tail {
                    RowTail::Closed => {
                        // Field absent from r2 with no tail. To unify,
                        // r1's presence must commit to Abs.
                        if let Err(_) =
                            self.unify_presence(span, &e1.presence, &crate::types::Presence::Abs)
                        {
                            return Err(TypeError::PropertyNotFound {
                                prop: prop.0.clone(),
                                obj_type: Type::Row(r2.clone()).to_string(),
                                span,
                            }
                            .into());
                        }
                    }
                    RowTail::Open(_) | RowTail::Recursive(_, _) => {
                        // Handled by the tail-extension below.
                    }
                },
                (None, Some(e2)) => match &r1.tail {
                    RowTail::Closed => {
                        if let Err(_) =
                            self.unify_presence(span, &e2.presence, &crate::types::Presence::Abs)
                        {
                            return Err(TypeError::PropertyNotFound {
                                prop: prop.0.clone(),
                                obj_type: Type::Row(r1.clone()).to_string(),
                                span,
                            }
                            .into());
                        }
                    }
                    RowTail::Open(_) | RowTail::Recursive(_, _) => {}
                },
                (None, None) => unreachable!(),
            }
        }

        // Unify tails
        match (&r1.tail, &r2.tail) {
            (RowTail::Closed, RowTail::Closed) => {
                // Under presence polymorphism the per-field pass above
                // is sufficient: any field present on one side and not
                // the other has already been unified against `Abs` (or
                // errored). A raw length comparison would reject pairs
                // that the field-by-field unification accepts (e.g.,
                // `{a}` against `{a, b?}` where `b`'s presence binds
                // to `Abs`).
                Ok(())
            }

            (RowTail::Open(v1), RowTail::Open(v2)) if v1 == v2 => Ok(()),

            (RowTail::Open(TVarName::Flex(id)), RowTail::Closed) => {
                // Bind the row variable to an empty row
                let extra_props: BTreeMap<PropName, FieldEntry> = r2
                    .props
                    .iter()
                    .filter(|(k, _)| !r1.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                if extra_props.is_empty() {
                    self.extend_subst(
                        span,
                        TVarName::Flex(*id),
                        Type::Row(RowType::empty_closed()),
                    )
                } else {
                    self.extend_subst(
                        span,
                        TVarName::Flex(*id),
                        Type::Row(RowType::closed_entries(extra_props)),
                    )
                }
            }

            (RowTail::Closed, RowTail::Open(TVarName::Flex(id))) => {
                // Symmetric case
                let extra_props: BTreeMap<PropName, FieldEntry> = r1
                    .props
                    .iter()
                    .filter(|(k, _)| !r2.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                if extra_props.is_empty() {
                    self.extend_subst(
                        span,
                        TVarName::Flex(*id),
                        Type::Row(RowType::empty_closed()),
                    )
                } else {
                    self.extend_subst(
                        span,
                        TVarName::Flex(*id),
                        Type::Row(RowType::closed_entries(extra_props)),
                    )
                }
            }

            (RowTail::Open(TVarName::Flex(id1)), RowTail::Open(TVarName::Flex(id2))) => {
                // Path-compress both tail vars to their union-find
                // roots. The existing v1 == v2 short-circuit at
                // RowTail::Open(v1) | RowTail::Open(v2) above only
                // catches the trivially-equal case. Two tail vars
                // that *transitively* reference the same root via a
                // Var → Var → … chain in the substitution would
                // otherwise fall into the fresh-tail dance below,
                // bind both ends, and on the next collision re-enter
                // unify_rows on the resulting rows with two *new*
                // fresh tails — the htmx divergence cycle observed
                // in gdb. Catching "same equivalence class" here
                // short-circuits that loop the same way the v1 == v2
                // check does for the trivial case.
                let root1 = match self.main_subst.resolve(&TVarName::Flex(*id1)) {
                    Some(Type::Var(TVarName::Flex(r))) => r,
                    None => *id1,
                    // If the chain ends at a structural type or a
                    // skolem, fall through to the fresh-tail dance
                    // with the original ids; the next unification
                    // step will handle the structural case via the
                    // normal Var-vs-structure path.
                    _ => *id1,
                };
                let root2 = match self.main_subst.resolve(&TVarName::Flex(*id2)) {
                    Some(Type::Var(TVarName::Flex(r))) => r,
                    None => *id2,
                    _ => *id2,
                };
                if root1 == root2 {
                    return Ok(());
                }

                // Calculate extra properties for each side
                let extra1: BTreeMap<PropName, FieldEntry> = r2
                    .props
                    .iter()
                    .filter(|(k, _)| !r1.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                let extra2: BTreeMap<PropName, FieldEntry> = r1
                    .props
                    .iter()
                    .filter(|(k, _)| !r2.props.contains_key(*k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                // Fast path: when both rows have the same prop set
                // (extras both empty), the standard Rémy fresh-tail
                // dance reduces to bookkeeping — we'd allocate a
                // fresh `γ` and bind `root1 → Row{∅, γ}`,
                // `root2 → Row{∅, γ}` purely to record that root1
                // and root2 now share an unknown extension. Just
                // union them instead: `root1 → Var(root2)` makes
                // them members of the same equivalence class with
                // one fewer variable. This is the union-find merge
                // operation (Tarjan 1975) and converts the htmx
                // divergence cycle — which spent its time
                // re-allocating γ's for repeatedly-unified copies
                // of the same htmx row — into a constant-time
                // operation.
                if extra1.is_empty() && extra2.is_empty() {
                    self.extend_subst(
                        span,
                        TVarName::Flex(root1),
                        Type::Var(TVarName::Flex(root2)),
                    )?;
                    return Ok(());
                }

                // Both open with at least one side extending the
                // other: standard Rémy fresh-tail dance.
                let fresh = self.fresh_flex();

                // Bind both row variables. Use the path-compressed
                // roots rather than the original ids so the binding
                // lands on the canonical representative of each
                // equivalence class.
                self.extend_subst(
                    span,
                    TVarName::Flex(root1),
                    Type::Row(RowType::open_entries(extra1, fresh.clone())),
                )?;
                self.extend_subst(
                    span,
                    TVarName::Flex(root2),
                    Type::Row(RowType::open_entries(extra2, fresh)),
                )?;

                Ok(())
            }

            (RowTail::Recursive(id1, args1), RowTail::Recursive(id2, args2)) if id1 == id2 => {
                // Same recursive type
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(span, a1, a2)?;
                }
                Ok(())
            }

            _ => Err(self.unification_error(span, &Type::Row(r1.clone()), &Type::Row(r2.clone()))),
        }
    }

    /// Create a recursive type when occurs check detects a row cycle.
    fn create_recursive_type(&mut self, span: Span, var: TVarId, ty: &Type) -> UnifyResult<()> {
        // Generate a new type ID
        let type_id = self.fresh_type_id();

        // Create the recursive type definition
        // The body is the type with the variable replaced by Named(type_id, [])
        let rec_ref = Type::Named(type_id, vec![]);

        // Create substitution to replace var with the recursive reference
        let mut subst = Subst::empty();
        subst.insert(TVarName::Flex(var), rec_ref.clone());
        let body = subst.apply(ty);

        let def = TypeDef::recursive(type_id, vec![], body);

        self.register_named_type(def);

        // Bind the original variable to the recursive type
        self.extend_subst(span, TVarName::Flex(var), rec_ref)
    }

    /// Create a unification error.
    pub(crate) fn unification_error(&self, span: Span, t1: &Type, t2: &Type) -> IntyError {
        let expected_origin = self
            .get_origin(t1)
            .cloned()
            .or_else(|| self.find_origin_through_subst(t1));
        let found_origin = self
            .get_origin(t2)
            .cloned()
            .or_else(|| self.find_origin_through_subst(t2));

        // Render brands by their declared name so a mismatch reads
        // `UserId` vs `OrderId` rather than `μ3` vs `μ4`.
        let mut ctx = crate::types::PrettyContext::with_nominal_names(self.nominal_names());

        TypeError::UnificationError {
            expected: ctx.format_type(t1),
            found: ctx.format_type(t2),
            span,
            context: None,
            expected_origin,
            found_origin,
        }
        .into()
    }

    /// Try to find an origin by looking through the substitution
    fn find_origin_through_subst(&self, ty: &Type) -> Option<crate::error::TypeOrigin> {
        // Look through the substitution to find if any type variable
        // was substituted to produce this type
        for (var, subst_ty) in self.main_subst.iter() {
            if subst_ty == ty {
                if let Some(origin) = self.type_origins.get(var) {
                    return Some(origin.clone());
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_same_primitive() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        assert!(state.unify(span, &Type::Number, &Type::Number).is_ok());
        assert!(state.unify(span, &Type::String, &Type::String).is_ok());
    }

    #[test]
    fn test_unify_tuples_congruence() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Same arity, components unify pairwise.
        let a = Type::Tuple(vec![Type::Number, Type::String]);
        let b = Type::Tuple(vec![Type::Number, Type::String]);
        assert!(state.unify(span, &a, &b).is_ok());

        // Component mismatch fails.
        let c = Type::Tuple(vec![Type::Number, Type::Boolean]);
        assert!(state.unify(span, &a, &c).is_err());

        // Different arity is a distinct type (no width subtyping).
        let d = Type::Tuple(vec![Type::Number, Type::String, Type::Boolean]);
        assert!(state.unify(span, &a, &d).is_err());

        // A tuple does not unify with an array.
        let arr = Type::array(Type::Number);
        assert!(state.unify(span, &a, &arr).is_err());

        // A fresh variable binds to a tuple.
        let v = state.fresh_type_var();
        assert!(state.unify(span, &v, &a).is_ok());
    }

    #[test]
    fn test_unify_different_primitives() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        assert!(state.unify(span, &Type::Number, &Type::String).is_err());
    }

    #[test]
    fn test_unify_var_with_type() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let var = Type::flex(0);
        assert!(state.unify(span, &var, &Type::Number).is_ok());

        // After unification, applying subst should give Number
        assert_eq!(state.zonk(&var), Type::Number);
    }

    #[test]
    fn test_unify_vars() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let v1 = Type::flex(0);
        let v2 = Type::flex(1);

        assert!(state.unify(span, &v1, &v2).is_ok());

        // Both should resolve to the same type after unification
        assert_eq!(state.zonk(&v1), state.zonk(&v2));
    }

    #[test]
    fn test_unify_functions() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let f1 = Type::simple_func(vec![Type::Number], Type::flex(0));
        let f2 = Type::simple_func(vec![Type::Number], Type::String);

        assert!(state.unify(span, &f1, &f2).is_ok());

        // a0 should be bound to String
        assert_eq!(state.zonk(&Type::flex(0)), Type::String);
    }

    #[test]
    fn test_unify_arity_mismatch() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let f1 = Type::simple_func(vec![Type::Number], Type::Number);
        let f2 = Type::simple_func(vec![Type::Number, Type::Number], Type::Number);

        assert!(state.unify(span, &f1, &f2).is_err());
    }

    /// Shape B: a callee with a presence-polymorphic trailing param
    /// unifies with a call site that supplies fewer or more
    /// arguments. The presence variable binds to `Abs` (caller omits
    /// the optional arg) or `Pre` (caller supplies it). Matches
    /// Garrigue 1994's labeled+optional argument unification.
    #[test]
    fn optional_param_unifies_with_short_call() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // callee: (Number, Number with presence φ) => String
        let phi = state.fresh_pvar();
        let callee = crate::types::Type::raw_func_with_params(
            None,
            vec![
                crate::types::FuncParam::required(crate::types::Type::Number),
                crate::types::FuncParam::optional(phi.clone(), crate::types::Type::Number),
            ],
            crate::types::Type::String,
        );
        let callee = Type::wrap_callable(callee);

        // call site: (Number) => ret (1 arg supplied)
        let ret = state.fresh_type_var();
        let call_shape = state.callable_row_open(None, vec![Type::Number], ret.clone());

        assert!(
            state.unify(span, &callee, &call_shape).is_ok(),
            "1-arg call against (a, b?) => c must succeed"
        );
        // The presence variable should have resolved to Abs.
        let resolved_phi = state
            .main_subst
            .resolve_presence(&crate::types::Presence::Var(phi.clone()));
        assert_eq!(
            resolved_phi,
            crate::types::Presence::Abs,
            "trailing optional param's presence should be Abs after a short call"
        );
        // And the return type should have unified to String.
        assert_eq!(state.zonk(&ret), Type::String);
    }

    #[test]
    fn optional_param_unifies_with_full_call() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // callee: (Number, Number with presence φ) => String
        let phi = state.fresh_pvar();
        let callee = crate::types::Type::raw_func_with_params(
            None,
            vec![
                crate::types::FuncParam::required(crate::types::Type::Number),
                crate::types::FuncParam::optional(phi.clone(), crate::types::Type::Number),
            ],
            crate::types::Type::String,
        );
        let callee = Type::wrap_callable(callee);

        // call site: (Number, Number) => ret (2 args supplied)
        let ret = state.fresh_type_var();
        let call_shape =
            state.callable_row_open(None, vec![Type::Number, Type::Number], ret.clone());

        assert!(
            state.unify(span, &callee, &call_shape).is_ok(),
            "2-arg call against (a, b?) => c must succeed"
        );
        // φ resolves to Pre.
        let resolved_phi = state
            .main_subst
            .resolve_presence(&crate::types::Presence::Var(phi));
        assert_eq!(resolved_phi, crate::types::Presence::Pre);
        assert_eq!(state.zonk(&ret), Type::String);
    }

    #[test]
    fn required_param_rejects_short_call() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // callee: (Number, Number) => String — both Pre
        let callee = Type::simple_func(
            vec![crate::types::Type::Number, crate::types::Type::Number],
            crate::types::Type::String,
        );

        let ret = state.fresh_type_var();
        let call_shape = state.callable_row_open(None, vec![Type::Number], ret);

        assert!(
            state.unify(span, &callee, &call_shape).is_err(),
            "1-arg call against (a, b) => c must error — second param is required"
        );
    }

    #[test]
    fn test_unify_closed_rows() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let r1 = Type::object([("x", Type::Number), ("y", Type::String)]);
        let r2 = Type::object([("x", Type::Number), ("y", Type::String)]);

        assert!(state.unify(span, &r1, &r2).is_ok());
    }

    #[test]
    fn test_unify_open_row_with_closed() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // {x: Number | a0} unified with {x: Number, y: String}
        let r1 = Type::object_open([("x", Type::Number)], TVarName::Flex(0));
        let r2 = Type::object([("x", Type::Number), ("y", Type::String)]);

        assert!(state.unify(span, &r1, &r2).is_ok());

        // The row variable should be bound to {y: String}
        let row_var = state.zonk(&Type::flex(0));
        if let Type::Row(row) = row_var {
            assert!(row.has_prop(&"y".into()));
        } else {
            panic!("Expected row type");
        }
    }

    #[test]
    fn test_occurs_check_simple() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Under the unified callable-row design, function values at top
        // level are `Row{<CALL>: Func{…}, Closed}`. A `var = func(var)`
        // unification therefore lands inside a row, which is the
        // documented "equirecursive" hatch — `is_inside_row_type`
        // routes it to `create_recursive_type` instead of the occurs
        // check. So this unification now succeeds, producing a μ-type.
        // To exercise the *non-row* occurs check that catches honest
        // cycles, we feed a raw `Type::Func` (sub-component form).
        let var = Type::flex(0);
        let func = Type::raw_static_func(vec![Type::flex(0)], Type::Number);

        assert!(state.unify(span, &var, &func).is_err());
    }

    #[test]
    fn test_unify_array_with_length_row() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should unify with {length: Number | a}
        let arr = Type::array(Type::Number);
        let row = Type::object_open([("length", Type::Number)], TVarName::Flex(0));

        assert!(state.unify(span, &arr, &row).is_ok());

        // The row variable should be bound to an empty closed row
        let row_var = state.zonk(&Type::flex(0));
        if let Type::Row(row) = row_var {
            assert!(row.props.is_empty());
            assert!(matches!(row.tail, RowTail::Closed));
        } else {
            panic!("Expected row type, got {:?}", row_var);
        }
    }

    #[test]
    fn test_unify_array_with_closed_length_row() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should unify with {length: Number}
        let arr = Type::array(Type::Number);
        let row = Type::object([("length", Type::Number)]);

        assert!(state.unify(span, &arr, &row).is_ok());
    }

    #[test]
    fn test_unify_array_with_wrong_property_fails() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should NOT unify with {foo: Number}
        let arr = Type::array(Type::Number);
        let row = Type::object([("foo", Type::Number)]);

        assert!(state.unify(span, &arr, &row).is_err());
    }

    #[test]
    fn test_unify_array_length_type_mismatch() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Array<Number> should NOT unify with {length: String}
        let arr = Type::array(Type::Number);
        let row = Type::object([("length", Type::String)]);

        assert!(state.unify(span, &arr, &row).is_err());
    }

    // --- Row-tail union shortcut (commit ae453b4) -----------------
    //
    // `unify_rows` `(Open α, Open β)` short-circuits to `α → Var(β)`
    // when both rows have the same prop names (extras are empty).
    // The literature-correct invariant is observable equality post-
    // unification: regardless of whether we allocated a fresh γ for
    // the common tail or just unioned the two tail vars, every
    // observer must see the two original rows resolve to the same
    // type. These tests pin that invariant.

    fn row_with_tail(
        props: &[(&str, crate::types::Type)],
        tail_id: crate::types::TVarId,
    ) -> crate::types::RowType {
        let entries: std::collections::BTreeMap<crate::types::PropName, crate::types::FieldEntry> =
            props
                .iter()
                .map(|(k, t)| {
                    (
                        crate::types::PropName((*k).to_string()),
                        crate::types::FieldEntry {
                            presence: crate::types::Presence::Pre,
                            ty: t.clone(),
                        },
                    )
                })
                .collect();
        crate::types::RowType::open_entries(entries, crate::types::TVarName::Flex(tail_id))
    }

    #[test]
    fn unify_open_open_same_shape_makes_rows_equal() {
        // Two rows with the same prop names and different open
        // tails. After unify_rows, applying the substitution to
        // either row must produce the same Type.
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let r1 = Type::Row(row_with_tail(
            &[("a", Type::Number), ("b", Type::String)],
            0,
        ));
        let r2 = Type::Row(row_with_tail(
            &[("a", Type::Number), ("b", Type::String)],
            1,
        ));

        state.unify(span, &r1, &r2).expect("same-shape rows unify");

        let r1_after = state.zonk(&r1);
        let r2_after = state.zonk(&r2);

        // The internal representation can vary (one tail might be
        // an alias of the other), but the resolved Types must be
        // equal under the substitution. `flatten_type` reads the
        // chain to fixed point — that's the observer the rest of
        // the system uses at boundaries.
        let f1 = state.flatten_type(&r1_after);
        let f2 = state.flatten_type(&r2_after);
        assert_eq!(f1, f2, "rows must resolve to the same type");
    }

    #[test]
    fn unify_open_open_same_shape_field_types_propagate() {
        // After the union, constraining one row's field type must
        // propagate to the other's. Bind α (in r1's `a` slot) to
        // a fresh tvar, then unify r2's `a` slot with Number — and
        // assert that the first tvar resolves to Number too.
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        // Use fresh tvars so InferState's id counter stays consistent.
        let tail1 = state.fresh_flex();
        let tail2 = state.fresh_flex();
        let field_a_name = state.fresh_flex();
        let field_a = Type::Var(field_a_name);

        let r1 = Type::Row(crate::types::RowType::open_entries(
            std::iter::once((
                crate::types::PropName("a".to_string()),
                crate::types::FieldEntry {
                    presence: crate::types::Presence::Pre,
                    ty: field_a.clone(),
                },
            ))
            .collect(),
            tail1,
        ));
        let r2 = Type::Row(crate::types::RowType::open_entries(
            std::iter::once((
                crate::types::PropName("a".to_string()),
                crate::types::FieldEntry {
                    presence: crate::types::Presence::Pre,
                    ty: Type::Number,
                },
            ))
            .collect(),
            tail2,
        ));

        state.unify(span, &r1, &r2).expect("same-shape rows unify");

        // field_a was the type of r1's `a` field; it must have
        // unified with Number through the shared prop loop.
        assert_eq!(state.zonk(&field_a), Type::Number);
    }

    #[test]
    fn unify_open_open_different_shape_allocates_fresh() {
        // The shortcut only fires when both extras are empty. When
        // they're not, the Rémy fresh-tail dance has to run —
        // verify both rows still resolve compatibly.
        let mut state = InferState::new();
        let span = Span::new(0, 0);

        let r1 = Type::Row(row_with_tail(&[("a", Type::Number)], 0));
        let r2 = Type::Row(row_with_tail(&[("b", Type::String)], 1));

        state
            .unify(span, &r1, &r2)
            .expect("rows with disjoint props unify via tail extension");

        // After unification, both rows must have observable types
        // that agree on every common field. We use flatten_type to
        // see the merged shape from either side.
        let f1 = state.flatten_type(&r1);
        let f2 = state.flatten_type(&r2);

        // Both should be Row types and report `a: Number` and
        // `b: String` after the tail extension.
        let (props1, props2) = match (&f1, &f2) {
            (Type::Row(rr1), Type::Row(rr2)) => (rr1.props.clone(), rr2.props.clone()),
            _ => panic!("expected both sides to be Row, got {:?} and {:?}", f1, f2),
        };
        assert_eq!(props1, props2, "merged row shape must match on both sides");
        assert!(props1.contains_key(&crate::types::PropName("a".to_string())));
        assert!(props1.contains_key(&crate::types::PropName("b".to_string())));
    }

    // === Nominal types ===
    //
    // A nominal type carries brand identity: it unifies only with the
    // same brand id, never with its representation or with a distinct
    // brand of identical shape. Field access still sees through to the
    // representation. See `docs/pyi-import-mapping.md` §8.

    use crate::types::TypeDef;

    /// Declare a nominal type with the given representation and return a
    /// nullary reference to it.
    fn declare_nominal(state: &mut InferState, name: &str, repr: Type) -> Type {
        let id = state.fresh_type_id();
        state.register_named_type(TypeDef::nominal(id, name, vec![], repr));
        Type::Named(id, vec![])
    }

    #[test]
    fn nominal_unifies_with_itself() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let user_id = declare_nominal(&mut state, "UserId", Type::Number);
        assert!(state.unify(span, &user_id, &user_id.clone()).is_ok());
    }

    #[test]
    fn nominal_does_not_unify_with_its_representation() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let user_id = declare_nominal(&mut state, "UserId", Type::Number);
        // The whole point of a brand: a raw Number is not a UserId.
        assert!(state.unify(span, &user_id, &Type::Number).is_err());
        assert!(state.unify(span, &Type::Number, &user_id).is_err());
    }

    #[test]
    fn distinct_nominals_with_same_shape_do_not_unify() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let user_id = declare_nominal(&mut state, "UserId", Type::Number);
        let order_id = declare_nominal(&mut state, "OrderId", Type::Number);
        assert!(state.unify(span, &user_id, &order_id).is_err());
    }

    #[test]
    fn nominal_field_access_sees_through_to_representation() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        // nominal Point = {x: Number, y: Number}
        let repr = Type::object([("x", Type::Number), ("y", Type::Number)]);
        let point = declare_nominal(&mut state, "Point", repr);
        // `p.x` reads through the brand to the representation row.
        let x_ty = state
            .infer_member_on_type(&point, "x", span)
            .expect("transparent field access on nominal type");
        assert_eq!(state.zonk(&x_ty), Type::Number);
    }

    #[test]
    fn equirecursive_named_still_unrolls() {
        // Regression guard: the nominal change must not disturb the
        // equi-recursive path. A non-nominal named type still unifies
        // structurally with its representation.
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let id = state.fresh_type_id();
        state.register_named_type(TypeDef::recursive(id, vec![], Type::Number));
        let named = Type::Named(id, vec![]);
        assert!(state.unify(span, &named, &Type::Number).is_ok());
    }

    // === Nominal × open-row constraint (#71) ===
    //
    // The hoisted-unify path in `infer_stmt_list` meets a brand with the
    // open-tailed row constraints accumulated by use sites before the
    // declaration was inferred. Without unrolling that direction, the
    // canonical `ROOT = Path("..."); def f(): return ROOT.read_text()`
    // pattern fails to type-check. Closed rows (user-introduced values)
    // are still rejected, preserving nominal safety.

    #[test]
    fn nominal_unrolls_for_open_row_constraint() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        // nominal Point = {x: Number, y: Number}
        let repr = Type::object([("x", Type::Number), ("y", Type::Number)]);
        let point = declare_nominal(&mut state, "Point", repr);
        // Open-tailed row demanding `x: Number` — the shape `rows.rs`
        // synthesizes when an unresolved object is member-accessed.
        let tail = state.fresh_flex();
        let constraint = Type::object_open([("x", Type::Number)], tail);
        assert!(state.unify(span, &point, &constraint).is_ok());
    }

    #[test]
    fn nominal_rejects_closed_row_value() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        // nominal Point = {x: Number, y: Number}
        let repr = Type::object([("x", Type::Number), ("y", Type::Number)]);
        let point = declare_nominal(&mut state, "Point", repr);
        // A user-introduced value of structurally-equivalent shape is a
        // *closed* row — it must not collapse into the brand.
        let value = Type::object([("x", Type::Number), ("y", Type::Number)]);
        assert!(state.unify(span, &point, &value).is_err());
        assert!(state.unify(span, &value, &point).is_err());
    }

    #[test]
    fn nominal_open_row_constraint_with_wrong_field_type_fails() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let repr = Type::object([("x", Type::Number), ("y", Type::Number)]);
        let point = declare_nominal(&mut state, "Point", repr);
        // Field name matches but type disagrees — unrolling exposes the
        // mismatch through the structural unification.
        let tail = state.fresh_flex();
        let constraint = Type::object_open([("x", Type::String)], tail);
        assert!(state.unify(span, &point, &constraint).is_err());
    }

    #[test]
    fn nominal_open_row_missing_field_fails() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let repr = Type::object([("x", Type::Number)]);
        let point = declare_nominal(&mut state, "Point", repr);
        // Demanding a property the instance row doesn't have still fails:
        // unrolling produces a closed `{x: Number}` which can't satisfy
        // `{missing: T | _}`.
        let tail = state.fresh_flex();
        let constraint = Type::object_open([("missing", Type::Number)], tail);
        assert!(state.unify(span, &point, &constraint).is_err());
    }
}
