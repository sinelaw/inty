//! Inference state management.
//!
//! This module provides the `InferState` struct which tracks:
//! - Fresh variable generation
//! - Current substitution
//! - Named recursive type definitions
//! - Pending type class constraints

use std::collections::HashMap;

use super::var_table::{TrailMark, VarTable};
use super::InferResult;

/// Erase flex-var ids and presence-var ids to a single canonical
/// form so two types that differ only in unification-variable
/// naming compare equal. Used by the debug-only mirror-invariant
/// probe in [`InferState::assert_mirror_consistent`]; production
/// builds don't reference it.
#[cfg(debug_assertions)]
fn structural_norm(ty: &Type) -> Type {
    match ty {
        Type::Var(TVarName::Flex(_)) => Type::Var(TVarName::Flex(0)),
        Type::Var(TVarName::Skolem(id)) => Type::Var(TVarName::Skolem(*id)),
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type.as_ref().map(|t| Box::new(structural_norm(t))),
            params: params.iter().map(structural_norm).collect(),
            ret: Box::new(structural_norm(ret)),
        },
        Type::Row(row) => Type::Row(crate::types::RowType {
            props: row
                .props
                .iter()
                .map(|(k, e)| {
                    (
                        k.clone(),
                        crate::types::FieldEntry {
                            // Normalise presence to either Pre/Abs
                            // or a single canonical Var so the probe
                            // doesn't fire on differently-named
                            // presence vars.
                            presence: match &e.presence {
                                crate::types::Presence::Var(_) => crate::types::Presence::Var(
                                    crate::types::PVarName::Flex(0),
                                ),
                                other => other.clone(),
                            },
                            ty: structural_norm(&e.ty),
                        },
                    )
                })
                .collect(),
            tail: match &row.tail {
                crate::types::RowTail::Open(TVarName::Flex(_)) => {
                    crate::types::RowTail::Open(TVarName::Flex(0))
                }
                other => other.clone(),
            },
        }),
        Type::Array(elem) => Type::Array(Box::new(structural_norm(elem))),
        Type::Promise(inner) => Type::Promise(Box::new(structural_norm(inner))),
        Type::Map(value) => Type::Map(Box::new(structural_norm(value))),
        Type::Named(id, args) => Type::Named(*id, args.iter().map(structural_norm).collect()),
        Type::Union(members) => Type::Union(members.iter().map(structural_norm).collect()),
        other => other.clone(),
    }
}
use crate::error::{IntyError, TypeOrigin};
use crate::lexer::Span;
use crate::types::{
    ClassName, LitValue, QualType, RowTail, Subst, Substitutable, TVarId, TVarName, TidyEnv, Type,
    TypeDef, TypeId, TypePred, TypeScheme,
};

/// Type class definition with instances.
#[derive(Debug, Clone)]
pub struct TypeClass {
    pub name: ClassName,
    pub instances: Vec<TypeScheme>,
}

/// A pending constraint that needs to be resolved.
#[derive(Debug, Clone)]
pub struct PendingConstraint {
    pub pred: TypePred,
    pub span: Span,
}

/// A non-fatal diagnostic raised during inference. Warnings are
/// collected on `InferState` and surfaced after inference completes;
/// they do not abort type-checking.
#[derive(Debug, Clone)]
pub struct InferWarning {
    pub span: Span,
    pub message: String,
}

/// User-facing knobs for inference behaviour.
///
/// The defaults match inty's previous hardcoded behaviour so that
/// `InferConfig::default()` is a drop-in for callers that don't care
/// about policy. Each field is documented with what's affected when
/// the flag is flipped.
#[derive(Clone, Debug)]
pub struct InferConfig {
    /// Emit a non-fatal warning when a `switch` lacks a `default` arm
    /// and doesn't cover every literal of a closed-union discriminant.
    /// Default: `true` (matches phase-6 design-doc behaviour).
    pub exhaustiveness_warnings: bool,

    /// Generalise mutable container literals (arrays / objects) bound
    /// with `var` if all their elements are syntactic values. Default:
    /// `false` (the value-restriction default), matching what inty
    /// shipped before this knob existed. Setting to `true` is unsound
    /// in the presence of indexed assignment — the option exists so
    /// the meta-tests can exercise the looser regime.
    pub generalize_mutable_var_containers: bool,
}

impl Default for InferConfig {
    fn default() -> Self {
        InferConfig {
            exhaustiveness_warnings: true,
            generalize_mutable_var_containers: false,
        }
    }
}

/// Inference state tracking type variables, substitution, and constraints.
pub struct InferState {
    /// Counter for generating fresh type variables.
    name_source: TVarId,

    /// Counter for generating fresh presence variables (Remy '94).
    /// Lives in a namespace separate from `name_source`.
    pvar_source: crate::types::PVarId,

    /// Current substitution from unification.
    pub main_subst: Subst,

    /// Union-Find variable table mirroring `main_subst` (Step 2 of
    /// `docs/destructive-unification-plan.md`). Every write to
    /// `main_subst` (`extend_subst`, `rebind_var`) is mirrored here;
    /// every rollback site (`subsume`, `subsume_either`, `join`)
    /// snapshots the trail alongside cloning `main_subst` and
    /// restores both on failure. Reads still go through `main_subst`
    /// — Step 3 of the plan flips them over to
    /// `crate::infer::zonk::zonk(&mut state.var_table, ...)`,
    /// dropping `main_subst` when every reader has migrated.
    pub var_table: VarTable,

    /// Named type definitions for recursive types.
    pub named_types: HashMap<TypeId, TypeDef>,

    /// Counter for generating fresh type IDs.
    type_id_source: TypeId,

    /// Type class definitions.
    pub type_classes: HashMap<ClassName, TypeClass>,

    /// Pending type class constraints to resolve.
    pub pending_constraints: Vec<PendingConstraint>,

    /// Inferred types for declarations, keyed by span start position.
    /// Used for decorating the AST with type annotations.
    pub decl_types: HashMap<usize, Type>,

    /// Generalised schemes for declarations whose binding was
    /// generalised (`var`, `function`, etc. at top level or inside
    /// nested scopes). Keyed by span start position, parallel to
    /// `decl_types`. Lets the LSP/inlay-hint path surface type-class
    /// predicates (`where Plus a`) even after the enclosing scope's
    /// env has been discarded.
    pub decl_schemes: HashMap<usize, TypeScheme>,

    /// Type origins for error reporting.
    pub type_origins: HashMap<TVarName, TypeOrigin>,

    /// Non-fatal warnings collected during inference.
    /// Currently used by switch-exhaustiveness; consumers can iterate
    /// over them after inference completes.
    pub warnings: Vec<InferWarning>,

    /// Errors accumulated during inference. The `Type::Error` recovery
    /// path lets `infer_stmt_list` keep going after a failed
    /// statement, so multiple errors can surface from a single
    /// inference run. The public `infer_program*` API still returns
    /// the first error via `Result::Err` for backwards compatibility;
    /// consumers wanting the full set (e.g. the CLI) drain this vec
    /// after the call completes.
    pub errors: Vec<IntyError>,

    /// Policy knobs. See `InferConfig`.
    pub config: InferConfig,

    /// User-defined generic type aliases, keyed by the alias name.
    /// Each entry stores its type-parameter list (as fresh skolemised
    /// variable IDs introduced when the alias body was first parsed)
    /// and the parsed body type. Application is by capture-avoiding
    /// substitution: instantiate fresh copies of the parameters, walk
    /// the body cloning structure, and substitute argument types in
    /// for the parameters.
    pub type_aliases: HashMap<String, AliasDef>,
}

/// State captured by [`InferState::snapshot_inference`] and consumed
/// by [`InferState::restore_snapshot`]. Crate-private so the
/// snapshot/restore pair is the only way to use it.
#[derive(Debug, Clone)]
pub(crate) struct InferSnapshot {
    pub(crate) subst: Subst,
    pub(crate) constraints: Vec<PendingConstraint>,
    pub(crate) trail: TrailMark,
}

/// A parsed generic type alias. Treated as not-nominal: applying
/// `Foo<X>` produces the same type as inlining `Foo`'s body with
/// `X` substituted for the parameter, so unification is unaware of
/// alias identity.
#[derive(Debug, Clone)]
pub struct AliasDef {
    /// Type-parameter variable IDs (used in `body`).
    pub params: Vec<u32>,
    /// Parsed body type with `params` appearing as `Type::flex(id)`.
    pub body: Type,
}

impl Default for InferState {
    fn default() -> Self {
        Self::new()
    }
}

impl InferState {
    /// Create a new inference state with default policy.
    pub fn new() -> Self {
        Self::with_config(InferConfig::default())
    }

    /// Create a new inference state with the given policy.
    pub fn with_config(config: InferConfig) -> Self {
        InferState {
            name_source: 0,
            pvar_source: 0,
            main_subst: Subst::empty(),
            var_table: VarTable::new(),
            named_types: HashMap::new(),
            type_id_source: 0,
            type_classes: HashMap::new(),
            pending_constraints: Vec::new(),
            decl_types: HashMap::new(),
            decl_schemes: HashMap::new(),
            type_origins: HashMap::new(),
            warnings: Vec::new(),
            errors: Vec::new(),
            config,
            type_aliases: HashMap::new(),
        }
    }

    /// Record an inference error and continue. Used by `infer_stmt_list`
    /// when `Type::Error` recovery lets us keep type-checking past a
    /// failing statement. The first call's error is what the public
    /// `infer_program*` API returns via `Err`; later errors are only
    /// visible to callers that drain `errors` after the run.
    pub fn push_error(&mut self, err: IntyError) {
        self.errors.push(err);
    }

    /// Drain accumulated errors, leaving the state empty. The CLI calls
    /// this after `infer_program_with_env` to report every error,
    /// not just the first.
    pub fn take_errors(&mut self) -> Vec<IntyError> {
        std::mem::take(&mut self.errors)
    }

    /// Push a non-fatal warning. Called from inference paths that detect
    /// suspicious-but-not-broken patterns (e.g. non-exhaustive switch).
    pub fn warn(&mut self, span: Span, message: impl Into<String>) {
        self.warnings.push(InferWarning {
            span,
            message: message.into(),
        });
    }

    /// Record the origin of a type variable (only if higher priority than existing)
    pub fn record_origin(&mut self, var: TVarName, origin: TypeOrigin) {
        self.type_origins
            .entry(var)
            .and_modify(|existing| {
                if origin.priority() > existing.priority() {
                    *existing = origin.clone();
                }
            })
            .or_insert(origin);
    }

    /// Get the origin of a type
    pub fn get_origin(&self, ty: &Type) -> Option<&TypeOrigin> {
        if let Type::Var(var) = ty {
            self.type_origins.get(var)
        } else {
            // For non-variable types, look for origins in contained type variables
            self.find_origin_in_type(ty)
        }
    }

    /// Find an origin by looking through the type structure
    fn find_origin_in_type(&self, ty: &Type) -> Option<&TypeOrigin> {
        match ty {
            Type::Var(var) => self.type_origins.get(var),
            Type::Func {
                this_type,
                params,
                ret,
            } => this_type
                .as_ref()
                .and_then(|t| self.find_origin_in_type(t))
                .or_else(|| params.iter().find_map(|p| self.find_origin_in_type(p)))
                .or_else(|| self.find_origin_in_type(ret)),
            Type::Row(row) => row
                .props
                .values()
                .find_map(|e| self.find_origin_in_type(&e.ty))
                .or_else(|| {
                    if let RowTail::Open(var) = &row.tail {
                        self.type_origins.get(var)
                    } else {
                        None
                    }
                }),
            Type::Array(elem) => self.find_origin_in_type(elem),
            Type::Promise(inner) => self.find_origin_in_type(inner),
            Type::Map(value) => self.find_origin_in_type(value),
            Type::Named(_, args) => args.iter().find_map(|a| self.find_origin_in_type(a)),
            Type::Union(members) => members.iter().find_map(|m| self.find_origin_in_type(m)),
            _ => None,
        }
    }

    /// Get a human-readable name for a type based on its origin
    pub fn type_name_from_origin(&self, ty: &Type) -> Option<String> {
        self.get_origin(ty).map(|origin| match origin {
            TypeOrigin::Variable { name, .. } => format!("typeof({})", name),
            TypeOrigin::Parameter { param_name, .. } => format!("typeof({})", param_name),
            TypeOrigin::PropertyAccess { property, .. } => format!("typeof(.{})", property),
            TypeOrigin::Literal { value, .. } => format!("typeof({})", value),
            _ => origin.description(),
        })
    }

    /// Record an inferred type for a declaration at the given span.
    pub fn record_decl_type(&mut self, span: Span, ty: Type) {
        self.decl_types.insert(span.start, ty);
    }

    /// Look up the inferred type for a declaration by span.
    pub fn get_decl_type(&self, span: Span) -> Option<&Type> {
        self.decl_types.get(&span.start)
    }

    /// Record the generalised scheme for a declaration at the given
    /// span. Companion to [`record_decl_type`] — the type goes into
    /// `decl_types`, the scheme (with quantifiers and predicates) goes
    /// here. Monomorphic bindings don't need to call this.
    pub fn record_decl_scheme(&mut self, span: Span, scheme: TypeScheme) {
        self.decl_schemes.insert(span.start, scheme);
    }

    /// Look up the generalised scheme for a declaration by span.
    /// Returns `None` for bindings that weren't generalised.
    pub fn get_decl_scheme(&self, span: Span) -> Option<&TypeScheme> {
        self.decl_schemes.get(&span.start)
    }

    /// Generate a fresh flexible type variable.
    ///
    /// Also reserves an `Unbound` cell in [`Self::var_table`] keyed
    /// at the same `TVarId` so the Union-Find mirror of `main_subst`
    /// stays dense. `name_source` is incremented alongside
    /// `var_table.fresh()`; the two counters are invariant-equal.
    pub fn fresh_flex(&mut self) -> TVarName {
        let id = self.var_table.fresh();
        debug_assert_eq!(
            id, self.name_source,
            "var_table id must match name_source"
        );
        self.name_source = id + 1;
        TVarName::Flex(id)
    }

    /// Generate a fresh skolem (rigid) type variable.
    ///
    /// Skolems are never looked up via the table — they're rigid by
    /// construction — but they share the `TVarId` namespace with
    /// flex variables, so we reserve a cell to keep the namespace
    /// dense. The cell stays `Unbound` for the life of the
    /// inference run and is never read.
    pub fn fresh_skolem(&mut self) -> TVarName {
        let id = self.var_table.fresh();
        debug_assert_eq!(
            id, self.name_source,
            "var_table id must match name_source"
        );
        self.name_source = id + 1;
        TVarName::Skolem(id)
    }

    /// Generate a fresh type variable (as a Type).
    pub fn fresh_type_var(&mut self) -> Type {
        Type::Var(self.fresh_flex())
    }

    /// Generate a fresh flexible presence variable (Remy '94).
    pub fn fresh_pvar(&mut self) -> crate::types::PVarName {
        let id = self.pvar_source;
        self.pvar_source += 1;
        crate::types::PVarName::Flex(id)
    }

    /// Generate a fresh rigid (skolem) presence variable for subsumption.
    pub fn fresh_pvar_skolem(&mut self) -> crate::types::PVarName {
        let id = self.pvar_source;
        self.pvar_source += 1;
        crate::types::PVarName::Skolem(id)
    }

    /// Build an *open* callable row representing an "expected callable
    /// shape" with a fresh tail variable.
    ///
    /// Under the unified callable-row design, function VALUES (from JS
    /// function literals, annotations, builtin signatures) are CLOSED
    /// callable rows — `Row{<CALL>: Func, Closed}` — with no extras.
    /// Function SHAPES (the "what fits here" type at a call site or as
    /// a higher-order parameter) are OPEN callable rows so they accept
    /// callable values that carry additional fields, like
    /// `arr.map(String)` where `String` is a constructor with statics.
    ///
    /// This is the standard row-polymorphism pattern applied to the
    /// `<CALL>` field. The fresh tail variable is later quantified by
    /// the caller's scheme generalisation, so each instantiation
    /// produces an independent tail.
    pub fn callable_row_open(
        &mut self,
        this_type: Option<Type>,
        params: Vec<Type>,
        ret: Type,
    ) -> Type {
        use crate::types::{PropName, RowType, CALLABLE_KEY};
        let func = match this_type {
            Some(t) => Type::raw_func(t, params, ret),
            None => Type::raw_static_func(params, ret),
        };
        let mut props = std::collections::BTreeMap::new();
        props.insert(PropName(CALLABLE_KEY.to_string()), func);
        let tail = self.fresh_flex();
        Type::Row(RowType::open(props, tail))
    }

    /// Get the next type variable ID (for type annotation parsing).
    pub fn next_var_id(&self) -> u32 {
        self.name_source
    }

    /// Advance the name source past the given id so subsequent
    /// `fresh_flex` calls don't collide. Used after a type-parser
    /// invocation that may have allocated its own ids beyond the
    /// state's view.
    ///
    /// Pads `var_table` with `Unbound` cells to match. The cells
    /// for the gap are never explicitly bound; they exist solely so
    /// `var_table.cells.len()` stays equal to `name_source`.
    pub fn bump_var_id_to(&mut self, id: u32) {
        while self.var_table.len() < id as usize {
            self.var_table.fresh();
        }
        if id > self.name_source {
            self.name_source = id;
        }
    }

    /// Get the next presence variable ID (for type annotation parsing).
    pub fn next_pvar_id(&self) -> u32 {
        self.pvar_source
    }

    /// Advance the pvar source past the given id, mirroring
    /// `bump_var_id_to` for type variables.
    pub fn bump_pvar_id_to(&mut self, id: u32) {
        if id > self.pvar_source {
            self.pvar_source = id;
        }
    }

    /// Generate a fresh type ID for recursive types.
    pub fn fresh_type_id(&mut self) -> TypeId {
        let id = self.type_id_source;
        self.type_id_source += 1;
        id
    }

    /// Apply the current substitution to a type.
    ///
    /// `Type` callers (the common case) are routed through
    /// [`crate::infer::zonk::zonk`], which reads from the Union-Find
    /// `var_table` with Tarjan path compression. Non-Type callers
    /// (`Vec<Type>`, `Option<Type>`, `TypeScheme`, …) still go
    /// through the HashMap `main_subst`; flipping those is the
    /// remainder of Step 3 in
    /// `docs/destructive-unification-plan.md`.
    pub fn apply_subst<T: Substitutable>(&self, t: &T) -> T {
        self.main_subst.apply(t)
    }

    /// Type-only zonk through the Union-Find variable table. This
    /// is the destructive-unification replacement for
    /// `apply_subst(&Type)`. Prefer this over `apply_subst` at
    /// hot-path sites; the asymptotic cost is α(n) per variable
    /// lookup instead of HashMap-chain-length, and the win
    /// compounds in tight loops like `unify`.
    pub fn zonk(&mut self, t: &Type) -> Type {
        super::zonk::zonk(&mut self.var_table, &self.main_subst, t)
    }

    /// Snapshot the inference state for speculative work.
    ///
    /// Captures everything a rollback needs to restore:
    ///   - `main_subst` is cloned (Step 2 lives with the clone cost
    ///     — Step 3+ moves reads to `var_table` and drops the
    ///     clone),
    ///   - `pending_constraints` is cloned (the type-class solver
    ///     adds predicates that must not survive a failed branch),
    ///   - `var_table` records a trail mark; on restore the trail
    ///     pops back to it.
    ///
    /// Pair with [`Self::restore_snapshot`]. This is the canonical
    /// rollback discipline used by `subsume`, `subsume_either`,
    /// `join`, and the row-subsume / array-subsume sub-rules; every
    /// speculative path goes through it so the trail and the
    /// HashMap mirror stay in lockstep.
    pub(crate) fn snapshot_inference(&self) -> InferSnapshot {
        InferSnapshot {
            subst: self.main_subst.clone(),
            constraints: self.pending_constraints.clone(),
            trail: self.var_table.snapshot(),
        }
    }

    /// Restore a snapshot taken by [`Self::snapshot_inference`].
    pub(crate) fn restore_snapshot(&mut self, snap: InferSnapshot) {
        self.main_subst = snap.subst;
        self.pending_constraints = snap.constraints;
        self.var_table.restore(snap.trail);
        // Post-restore probe (debug only): the var_table and
        // main_subst should still agree on every key that survives
        // the rollback. Spot-check a handful — full-table sweep
        // would be quadratic in the var count.
        #[cfg(debug_assertions)]
        self.assert_mirror_consistent_sample();
    }

    /// Debug-only spot-check on the mirror invariant. Samples a
    /// handful of variables from `main_subst`'s domain and verifies
    /// `zonk(Var(α))` and `apply_subst(Var(α))` agree structurally.
    /// Used at restore-snapshot boundaries to catch drift introduced
    /// by a faulty rollback.
    #[cfg(debug_assertions)]
    fn assert_mirror_consistent_sample(&mut self) {
        let domain: Vec<TVarName> = self.main_subst.domain().into_iter().take(8).collect();
        for var in domain {
            self.assert_mirror_consistent(&var);
        }
    }

    /// Boundary-view of a type: like `apply_subst`, but also merges
    /// row tails that resolve to a row through the substitution.
    /// `apply_subst` is shallow on tails for performance during
    /// inference; callers that need the printable shape of a type
    /// (LSP hover/inlay hints, decorate.rs) want this instead. See
    /// `Subst::flatten` for the full rationale.
    pub fn flatten_type(&self, ty: &Type) -> Type {
        self.main_subst.flatten(ty)
    }

    /// Boundary-view of a scheme: flattens the body type and every
    /// type inside each predicate. Companion to
    /// [`Self::flatten_type`].
    pub fn flatten_scheme(&self, scheme: &TypeScheme) -> TypeScheme {
        let ty = self.main_subst.flatten(&scheme.body.ty);
        let preds: Vec<TypePred> = scheme
            .body
            .preds
            .iter()
            .map(|p| TypePred {
                class: p.class,
                types: p
                    .types
                    .iter()
                    .map(|t| self.main_subst.flatten(t))
                    .collect(),
            })
            .collect();
        TypeScheme {
            vars: scheme.vars.clone(),
            pvars: scheme.pvars.clone(),
            body: QualType::with_preds(preds, ty),
        }
    }

    /// Canonical display form of a type: flatten through the
    /// substitution, then tidy with a fresh [`TidyEnv`] so the
    /// resulting `Type` carries small, traversal-ordered IDs. Any
    /// printer (CLI decorator, LSP hover, error message) handed
    /// this value produces the same string with no shared state.
    pub fn display_type(&self, ty: &Type) -> Type {
        let mut env = TidyEnv::new();
        env.tidy_type(&self.flatten_type(ty))
    }

    /// Canonical display form of a scheme. See [`Self::display_type`].
    pub fn display_scheme(&self, scheme: &TypeScheme) -> TypeScheme {
        let mut env = TidyEnv::new();
        env.tidy_scheme(&self.flatten_scheme(scheme))
    }

    /// Flatten + tidy `ty` into the supplied [`TidyEnv`]. Use this
    /// when you need *within-scope* consistency across several
    /// types — e.g. a function's scheme together with every
    /// binding inside it. Each call shares IDs the env has already
    /// assigned, so the same underlying tvar always tidies to the
    /// same canonical ID across calls.
    pub fn display_type_in(&self, env: &mut TidyEnv, ty: &Type) -> Type {
        env.tidy_type(&self.flatten_type(ty))
    }

    /// Flatten + tidy a scheme into the supplied env. Companion to
    /// [`Self::display_type_in`].
    pub fn display_scheme_in(&self, env: &mut TidyEnv, scheme: &TypeScheme) -> TypeScheme {
        env.tidy_scheme(&self.flatten_scheme(scheme))
    }

    /// Join two types into their least upper bound.
    ///
    /// Unlike [`Self::unify`], this never fails: if the two types disagree
    /// in a way unification can't reconcile, it returns the (normalised)
    /// union of the two. Used at branch-joining sites — ternary
    /// alternatives, if/else branches, array literal elements — where
    /// JavaScript naturally produces values of differing types and the
    /// type system needs to express "either".
    ///
    /// Side-effects: if unification succeeds, the substitution is updated
    /// as if the user had called `unify` directly. If it fails, the
    /// substitution is rolled back and a union is returned. This means
    /// `join` is safe to call speculatively at branch boundaries.
    pub fn join(&mut self, span: Span, t1: &Type, t2: &Type) -> Type {
        let t1 = self.zonk(t1);
        let t2 = self.zonk(t2);

        if t1 == t2 {
            return t1;
        }

        // Literal-with-base subsumption is decided at the join level
        // (not via unify): "a" | String → String, even though unify
        // accepts "a" ~ String for assignment-from-narrowed paths.
        if let Type::Literal(lit) = &t1 {
            if lit.base_type() == t2 {
                return t2;
            }
        }
        if let Type::Literal(lit) = &t2 {
            if lit.base_type() == t1 {
                return t1;
            }
        }

        // If either side is already a union, we don't try to unify (which
        // would just fail) — we fold members together instead. This also
        // makes `join` associative when chained over a list of types.
        if matches!(t1, Type::Union(_)) || matches!(t2, Type::Union(_)) {
            let mut all: Vec<Type> = Vec::new();
            match t1 {
                Type::Union(m) => all.extend(m),
                other => all.push(other),
            }
            match t2 {
                Type::Union(m) => all.extend(m),
                other => all.push(other),
            }
            return Self::normalise_union_members(all);
        }

        // Try to unify with rollback. We restore the substitution and the
        // pending-constraints list on failure so a join attempt has no
        // observable side-effect when it falls back to the union path.
        let snap = self.snapshot_inference();

        if self.unify(span, &t1, &t2).is_ok() {
            return self.zonk(&t1);
        }

        self.restore_snapshot(snap);

        Self::normalise_union_members(vec![t1, t2])
    }

    /// Subsumption: succeed iff `sub` may be supplied where `sup` is
    /// expected. This is *not* unification — it's the directed
    /// "fits where" judgement used at call sites and other contexts
    /// that have an expected shape.
    ///
    /// The rule set, in priority order:
    /// 1. Try `unify`; on success commit. This covers HM equality,
    ///    flex binding, and the existing literal-vs-base + union-
    ///    membership shortcuts already baked into `unify`.
    /// 2. **S-UnionR** (Pierce TAPL 15.7 / Dunfield 2014 §3): if
    ///    `sup` is `⋃ τᵢ`, attempt `subsume(sub, τᵢ)` against each
    ///    arm with substitution rollback. Commit only when *exactly
    ///    one* arm subsumes — multiple-match silently picking the
    ///    first is order-dependent and a known footgun. Zero or two-
    ///    plus matches reports a unification error at `span`.
    ///
    /// Other subtyping rules (function variance, deep row width
    /// subsumption beyond what `unify_rows` already does) are left
    /// to grow into this judgement as use cases land.
    pub fn subsume(&mut self, span: Span, sub: &Type, sup: &Type) -> InferResult<()> {
        let sub = self.zonk(sub);
        let sup = self.zonk(sup);

        // Rule 0 (S-LitBase): `Lit(l) ≤ Base` is sound — every
        // singleton is a value of its base. This rule used to live
        // (symmetrically, hence unsoundly) in `unify`. It's a pure
        // subsumption rule and lives here. The reverse direction
        // `Base ≤ Lit` is intentionally absent.
        if let Type::Literal(lit) = &sub {
            if lit.base_type() == sup {
                return Ok(());
            }
        }

        // Rule 1: try unify with rollback so a failed attempt has
        // no observable side-effect on the substitution.
        let snap = self.snapshot_inference();
        if self.unify(span, &sub, &sup).is_ok() {
            return Ok(());
        }
        self.restore_snapshot(snap);

        // S-Row: structural row subsumption. With `Lit ≤ Base`
        // removed from `unify`, two rows that differ only in
        // a literal-vs-base position no longer unify directly —
        // recurse here so e.g. `{kind: Lit("circle"), r: Lit(10)}
        // ≤ {kind: Lit("circle"), r: Number}` succeeds via per-
        // field subsumption.
        if let (Type::Row(r1), Type::Row(r2)) = (&sub, &sup) {
            if r1.is_closed()
                && r2.is_closed()
                && r1.props.len() == r2.props.len()
                && r1.props.keys().eq(r2.props.keys())
            {
                let snap = self.snapshot_inference();
                let mut all_ok = true;
                for (k, sub_field) in &r1.props {
                    let sup_field = r2.props.get(k).expect("keys checked equal");
                    if self
                        .subsume(span, &sub_field.ty, &sup_field.ty)
                        .is_err()
                    {
                        all_ok = false;
                        break;
                    }
                }
                if all_ok {
                    return Ok(());
                }
                self.restore_snapshot(snap);
            }
        }

        // S-Array: covariant element subsumption.
        if let (Type::Array(e1), Type::Array(e2)) = (&sub, &sup) {
            let snap = self.snapshot_inference();
            if self.subsume(span, e1, e2).is_ok() {
                return Ok(());
            }
            self.restore_snapshot(snap);
        }

        // Rule 2a (S-UnionL): a union value subsumes into `sup` iff
        // every arm does. Sound by definition — a value of type
        // ⋃τᵢ may be any τᵢ at runtime, so each must fit.
        if let Type::Union(members) = &sub {
            for m in members {
                let m_resolved = self.zonk(m);
                self.subsume(span, &m_resolved, &sup)?;
            }
            return Ok(());
        }

        // Rule 2b (S-UnionR): pick a union arm.
        if let Type::Union(members) = &sup {
            let mut matching: Vec<usize> = Vec::new();
            for (i, m) in members.iter().enumerate() {
                let snap = self.snapshot_inference();
                let m_resolved = self.zonk(m);
                let ok = self.subsume(span, &sub, &m_resolved).is_ok();
                // Roll back on every probe; we re-run on the chosen
                // arm below so the committed substitution comes from
                // a single, deliberate call.
                self.restore_snapshot(snap);
                if ok {
                    matching.push(i);
                    if matching.len() > 1 {
                        break;
                    }
                }
            }
            if matching.len() == 1 {
                let chosen = self.zonk(&members[matching[0]]);
                return self.subsume(span, &sub, &chosen);
            }
            // 0 → no arm fits; >1 → ambiguous. Both fall through to
            // the same error; the diagnostic is best-effort and uses
            // the original sub/sup pair so the user sees the union.
        }

        Err(self.unification_error(span, &sub, &sup))
    }

    /// "Either-direction" subsumption used by symmetric operators
    /// like `===`, `!==`, and ordering comparisons, where the two
    /// operands just need to have a common possible value — neither
    /// flow-direction is privileged. Try `subsume(t1, t2)` then
    /// `subsume(t2, t1)`; commit on the first one that succeeds, fail
    /// with the original error if neither does.
    pub fn subsume_either(&mut self, span: Span, t1: &Type, t2: &Type) -> InferResult<()> {
        let snap = self.snapshot_inference();
        if self.subsume(span, t1, t2).is_ok() {
            return Ok(());
        }
        self.restore_snapshot(snap);
        self.subsume(span, t2, t1)
    }

    /// Normalise a list of would-be union members applying the
    /// literal-subsumption rule: a literal type is dropped from the union
    /// when its base type (`Number`/`String`/`Boolean`) is also present
    /// (e.g. `"a" | String` collapses to `String`, but `"a" | "b"` stays
    /// a closed literal union).
    pub(crate) fn normalise_union_members(members: Vec<Type>) -> Type {
        let mut has_number = false;
        let mut has_string = false;
        let mut has_boolean = false;
        for m in &members {
            match m {
                Type::Number => has_number = true,
                Type::String => has_string = true,
                Type::Boolean => has_boolean = true,
                _ => {}
            }
        }

        let filtered: Vec<Type> = members
            .into_iter()
            .filter(|m| match m {
                Type::Literal(LitValue::String(_)) => !has_string,
                Type::Literal(LitValue::Number(_)) => !has_number,
                Type::Literal(LitValue::Bool(_)) => !has_boolean,
                _ => true,
            })
            .collect();

        Type::union(filtered)
    }

    /// Extend the substitution with a new binding.
    ///
    /// `Subst::compose` keeps the existing binding on key
    /// collision, which silently drops constraints when a row tail
    /// variable acquires a *second* row constraint after `unify_rows`
    /// already bound it from a *first* one. The fix can't live in
    /// `compose` itself (`compose` runs on every existing binding on
    /// every extend, so a deep merge there blows up combinatorially —
    /// infernu's equivalent gets away with the same shape only
    /// because Haskell laziness defers the work). Instead, the
    /// caller of `extend_subst` is the right place to handle a
    /// collision: unify the new value with the existing one, so the
    /// substitution faithfully carries every constraint that was
    /// posed. Errors from that unification are propagated to the
    /// caller — silently dropping them lets a closed-row tail
    /// re-bind to an arbitrary row constraint, masking
    /// property-not-found errors at chained-method call sites.
    pub fn extend_subst(
        &mut self,
        span: crate::lexer::Span,
        var: TVarName,
        ty: Type,
    ) -> super::unify::UnifyResult<()> {
        // Path-compressing lookup. `resolve` chases Var → Var → …
        // chains and rewrites every visited entry to point at the
        // chain endpoint (Tarjan 1975). Subsequent collision checks
        // on any variable along that chain resolve in O(1).
        if let Some(existing) = self.main_subst.resolve(&var) {
            // Already bound — unify so we don't lose either side.
            return self.unify(span, &existing, &ty);
        }
        // Direct insert — no `Subst::compose` walk over the existing
        // substitution. The textbook Damas-Milner formulation
        // composes to keep the substitution idempotent (every RHS
        // already substituted-through), at O(N·S) per extend. We
        // skip that eager propagation: `Subst::resolve`'s path
        // compression collapses Var-chains on lookup, and
        // `apply_subst`'s recursive Var arm follows them
        // structurally — together they give the same observable
        // behaviour as compose, lazily, at O(α(N)) amortised per
        // lookup. This is the substitution-side half of destructive
        // unification (cf. OCaml `Btype`, GHC `TcMType`, rustc
        // `rustc_infer::infer::InferCtxt`); the type-variable
        // identity is still HashMap-keyed rather than a true
        // union-find table with rank, but the asymptotic cost
        // savings are the same. See
        // docs/destructive-unification-plan.md.
        // Mirror the binding into the Union-Find table so reads
        // through `crate::infer::zonk` see the same view as reads
        // through `apply_subst`. Step 3 will flip the reads over.
        self.mirror_extend(&var, &ty);
        self.main_subst.insert(var.clone(), ty.clone());
        // Invariant probe (debug only): after every binding, the
        // Union-Find table and the HashMap must agree on the
        // chain endpoint for `var`. apply_subst follows the chain
        // through main_subst; zonk-on-Type chases through the
        // table. The two must land at the same flex root (modulo
        // shallow row-tail semantics, which we don't probe here
        // — see `zonk_row_with_visited` for why row tails can
        // legitimately diverge in representation).
        #[cfg(debug_assertions)]
        self.assert_mirror_consistent(&var);
        Ok(())
    }

    /// Debug-only: verify that `zonk(Var(var))` and
    /// `apply_subst(Var(var))` agree on the chain endpoint
    /// (modulo intermediate variable id). The check is intentionally
    /// non-strict on row tails because `RowType::apply_subst` is
    /// shallow-on-one-hop while `zonk` chases through `find` to the
    /// root; the two representations are observationally equivalent
    /// for downstream unification but not bit-for-bit equal.
    #[cfg(debug_assertions)]
    fn assert_mirror_consistent(&mut self, var: &TVarName) {
        let TVarName::Flex(_) = var else { return };
        let ty_var = Type::Var(var.clone());
        let via_subst = self.main_subst.apply(&ty_var);
        let via_zonk = super::zonk::zonk(&mut self.var_table, &self.main_subst, &ty_var);
        // If either side reached a non-Var (a structured type), the
        // structures must match exactly. If both sides remain a Var,
        // they should at minimum be in the same equivalence class
        // — but we can't check that without a costly walk. For now,
        // assert structural equality except on row tails (which the
        // shallow/find divergence makes flaky).
        if matches!(&via_subst, Type::Var(_)) && matches!(&via_zonk, Type::Var(_)) {
            return; // both still free; can't probe further cheaply
        }
        debug_assert_eq!(
            structural_norm(&via_subst),
            structural_norm(&via_zonk),
            "mirror invariant: zonk/apply_subst disagree on bound chain for {:?}",
            var
        );
    }

    /// Mirror an `extend_subst` write into the Union-Find table.
    /// Always called *before* the corresponding `main_subst.insert`,
    /// so the contracts of `bind` / `union` apply: the root must be
    /// `Unbound`. The collision case is handled by `extend_subst`'s
    /// caller running `resolve(var)` first.
    fn mirror_extend(&mut self, var: &TVarName, ty: &Type) {
        use super::var_table::Resolution;
        // Only flex variables ever appear as the LHS of a binding in
        // this codebase — `unify`'s `var_bind` rule only fires on
        // `Flex(_)`. Skolems on the LHS would be a caller bug.
        let id = match var {
            TVarName::Flex(id) => *id,
            TVarName::Skolem(_) => return,
        };
        // Some test paths synthesise variable ids directly without
        // going through `fresh_flex`. Pad the table so the index is
        // in range; padding cells are `Unbound { level: 0 }` which is
        // the right starting point for a never-allocated variable.
        self.var_table.ensure_id(id);
        if let Type::Var(TVarName::Flex(other)) = ty {
            self.var_table.ensure_id(*other);
            let root_a = self.var_table.find(id);
            let root_b = self.var_table.find(*other);
            if root_a == root_b {
                return; // already in the same class
            }
            let res_a = self.var_table.root_resolution(root_a);
            let res_b = self.var_table.root_resolution(root_b);
            // Invariant we enforce on the mirror: at most one cell
            // in any equivalence class carries the structured
            // `Bound(_)` value; every other class member is a
            // `Link` to it. This is what keeps `zonk` cycle-free
            // for non-pathological inputs — if we instead *copied*
            // the bound value into both roots, two cells could end
            // up bound to types that mutually reference each other
            // and zonk would loop. The four cases below preserve
            // the invariant by linking rather than duplicating.
            match (&res_a, &res_b) {
                (Resolution::Unbound { .. }, Resolution::Unbound { .. }) => {
                    // Bias: point LHS → RHS. `extend_subst(α,
                    // Var(β))` is a directed binding in
                    // `main_subst` (`α → Var(β)`), so its chain
                    // endpoint via `apply_subst` is β. To keep
                    // `zonk` equivalent we make β the surviving
                    // root, not whichever rank picks. The union-
                    // by-rank optimisation costs us a constant
                    // factor here; the equivalence with
                    // `apply_subst` is worth more than the α(n)
                    // tightness on the chain length.
                    self.var_table.link_to_root(root_a, root_b);
                }
                (Resolution::Unbound { .. }, Resolution::Bound(_)) => {
                    // root_a is free, root_b owns the value. Link
                    // root_a → root_b so the value stays in exactly
                    // one cell.
                    self.var_table.link_to_root(root_a, root_b);
                }
                (Resolution::Bound(_), Resolution::Unbound { .. }) => {
                    self.var_table.link_to_root(root_b, root_a);
                }
                (Resolution::Bound(_), Resolution::Bound(_)) => {
                    // Both roots already bound. extend_subst's
                    // `resolve(&var)` at the call site is supposed
                    // to have caught this and recursed via `unify`
                    // — every code path that reaches mirror_extend
                    // should have a fresh, never-bound key on at
                    // least one side. If we ever observe this in
                    // practice, the mirror has drifted.
                    debug_assert!(
                        false,
                        "mirror_extend both-Bound: var_table has both roots bound \
                         but extend_subst's `resolve` didn't intercept. This \
                         indicates the var_table has aliased variables that \
                         main_subst does not — a real drift bug."
                    );
                }
                _ => {}
            }
            return;
        }
        // Variable-to-structured: bind the root iff still free.
        let root = self.var_table.find(id);
        match self.var_table.root_resolution(root) {
            Resolution::Unbound { .. } => {
                self.var_table.bind(root, ty.clone());
            }
            Resolution::Bound(_) => {
                // Reachable only if some prior `mirror_extend` (via
                // another alias of `id`) bound this root, but
                // `main_subst.resolve(&var)` at the call site
                // didn't see the alias in main_subst — a drift.
                debug_assert!(
                    false,
                    "mirror_extend Var-to-struct: root already Bound \
                     but extend_subst's `resolve` didn't intercept. \
                     Drift between var_table and main_subst."
                );
            }
            Resolution::Link(_) => {
                // `find` returns a root; `root_resolution(root)` can
                // never yield Link. Defensive.
                debug_assert!(false, "find returned a Link root");
            }
        }
    }

    /// Bind a presence variable to a presence. Same collision-as-unify
    /// discipline as `extend_subst` for type variables.
    pub fn extend_subst_presence(
        &mut self,
        span: crate::lexer::Span,
        pvar: crate::types::PVarName,
        pres: crate::types::Presence,
    ) -> super::unify::UnifyResult<()> {
        // Resolve through any existing chain first to avoid trivially
        // creating cycles.
        let resolved = self
            .main_subst
            .resolve_presence(&crate::types::Presence::Var(pvar.clone()));
        if !matches!(&resolved, crate::types::Presence::Var(v) if v == &pvar) {
            // Already bound — unify with the new presence instead.
            return self.unify_presence(span, &resolved, &pres);
        }
        // Occurs check: don't bind θ → Var(θ).
        if let crate::types::Presence::Var(other) = &pres {
            if other == &pvar {
                return Ok(());
            }
        }
        // Direct insert — same destructive-unification discipline as
        // `extend_subst` above; presence chains are followed lazily
        // by `resolve_presence`.
        self.main_subst.insert_presence(pvar, pres);
        Ok(())
    }

    /// Unify two presences. Implements the Remy '94 presence-level
    /// judgment: Pre~Pre and Abs~Abs are reflexive; Pre~Abs is an
    /// error; Var(theta) unifies with the other side by binding theta.
    pub fn unify_presence(
        &mut self,
        span: crate::lexer::Span,
        p1: &crate::types::Presence,
        p2: &crate::types::Presence,
    ) -> super::unify::UnifyResult<()> {
        use crate::types::Presence;
        let p1 = self.main_subst.resolve_presence(p1);
        let p2 = self.main_subst.resolve_presence(p2);
        match (&p1, &p2) {
            (Presence::Pre, Presence::Pre) | (Presence::Abs, Presence::Abs) => Ok(()),
            (Presence::Pre, Presence::Abs) | (Presence::Abs, Presence::Pre) => {
                Err(crate::error::TypeError::PresenceMismatch {
                    expected: if matches!(p1, Presence::Pre) {
                        "present"
                    } else {
                        "absent"
                    }
                    .to_string(),
                    found: if matches!(p2, Presence::Pre) {
                        "present"
                    } else {
                        "absent"
                    }
                    .to_string(),
                    span,
                }
                .into())
            }
            (Presence::Var(v1), Presence::Var(v2)) if v1 == v2 => Ok(()),
            (Presence::Var(v), other) | (other, Presence::Var(v)) if v.is_flex() => {
                self.extend_subst_presence(span, v.clone(), other.clone())
            }
            // Two distinct skolem pvars, or a skolem ~ concrete:
            // unification fails because the skolem was supposed to
            // remain abstract.
            _ => Err(crate::error::TypeError::PresenceMismatch {
                expected: format!("{:?}", p1),
                found: format!("{:?}", p2),
                span,
            }
            .into()),
        }
    }

    /// Override a type variable binding in the substitution.
    /// Unlike extend_subst, this replaces any existing binding for the variable.
    /// Used when we discover a more specific type for a variable that was
    /// previously bound to a less specific type (e.g., Row -> Array).
    pub fn rebind_var(&mut self, var: TVarName, ty: Type) {
        // Mirror into the var_table by direct cell-rewrite. We can't
        // use `bind` here because the root may already be `Bound`
        // (that's exactly why `rebind_var` exists). Rewrite the
        // root's cell, trail-logging the previous state so a future
        // rollback restores it.
        if let TVarName::Flex(id) = &var {
            self.var_table.ensure_id(*id);
            let root = self.var_table.find(*id);
            self.var_table.force_bind_root(root, ty.clone());
        }
        self.main_subst.insert(var, ty);
    }

    /// Register a named type definition.
    pub fn register_named_type(&mut self, def: TypeDef) {
        self.named_types.insert(def.id, def);
    }

    /// Look up a named type definition.
    pub fn get_named_type(&self, id: TypeId) -> Option<&TypeDef> {
        self.named_types.get(&id)
    }

    /// Unroll a named recursive type by substituting its definition.
    pub fn unroll_named(&self, id: TypeId, args: &[Type]) -> Option<Type> {
        let def = self.named_types.get(&id)?;

        // Create substitution from params to args
        let mut subst = Subst::empty();
        for (param, arg) in def.params.iter().zip(args.iter()) {
            subst.insert(param.clone(), arg.clone());
        }

        Some(subst.apply(&def.body))
    }

    /// Add a pending constraint.
    pub fn add_constraint(&mut self, pred: TypePred, span: Span) {
        self.pending_constraints
            .push(PendingConstraint { pred, span });
    }

    /// Register a type class.
    pub fn register_type_class(&mut self, class: TypeClass) {
        self.type_classes.insert(class.name.clone(), class);
    }

    /// Instantiate a type scheme with fresh flexible variables (both
    /// type and presence). Each use site sees independent presence
    /// variables, so a scheme like `<θ>{x:Number, y:θ(String)} -> R`
    /// can be called once supplying `y` and once omitting it.
    pub fn instantiate(&mut self, scheme: &TypeScheme) -> Type {
        if scheme.is_mono() {
            return scheme.body.ty.clone();
        }

        let mut subst = Subst::empty();
        for var in &scheme.vars {
            let fresh = self.fresh_type_var();
            subst.insert(var.clone(), fresh);
        }
        for pvar in &scheme.pvars {
            let fresh = self.fresh_pvar();
            subst.insert_presence(pvar.clone(), crate::types::Presence::Var(fresh));
        }

        // Also instantiate predicates as pending constraints
        for pred in &scheme.body.preds {
            let instantiated_pred = subst.apply(pred);
            // Note: We'd need a span here, for now we use a dummy
            self.pending_constraints.push(PendingConstraint {
                pred: instantiated_pred,
                span: Span::new(0, 0),
            });
        }

        subst.apply(&scheme.body.ty)
    }

    /// Skolemize a type scheme (for subsumption checking).
    /// Returns the skolem variables and the body type. Presence
    /// variables are also skolemized; if a caller needs the skolem
    /// pvars they can re-derive them from the substitution.
    pub fn skolemize(&mut self, scheme: &TypeScheme) -> (Vec<TVarName>, Type) {
        if scheme.is_mono() {
            return (vec![], scheme.body.ty.clone());
        }

        let mut skolems = Vec::new();
        let mut subst = Subst::empty();

        for var in &scheme.vars {
            let skolem = self.fresh_skolem();
            skolems.push(skolem.clone());
            subst.insert(var.clone(), Type::Var(skolem));
        }
        for pvar in &scheme.pvars {
            let skolem = self.fresh_pvar_skolem();
            subst.insert_presence(
                pvar.clone(),
                crate::types::Presence::Var(skolem),
            );
        }

        (skolems, subst.apply(&scheme.body.ty))
    }

    /// Generalize a type over free variables not in the environment.
    /// Also collects relevant predicates from pending_constraints.
    /// Generalizes over presence variables too (Remy '94), with the
    /// same env-difference rule.
    pub fn generalize(
        &mut self,
        env_free_vars: &std::collections::HashSet<TVarName>,
        ty: &Type,
    ) -> TypeScheme {
        // Flatten row tails through the substitution before
        // computing free vars. `apply_subst` is shallow on tails
        // for performance reasons; without flattening here, a
        // function whose parameter row picked up extra fields via
        // later property-access constraints would generalise to a
        // scheme that's missing those fields, letting calls with
        // incompatible argument shapes through. See
        // `Subst::flatten` for the full story.
        let ty = self.main_subst.flatten(ty);
        let ty_vars = ty.free_vars();
        let pvars = ty.free_pvars();

        // Sort by TVarName id so the scheme's quantification order is
        // deterministic. `ty.free_vars()` returns a HashSet, whose
        // iteration order isn't stable even within a process — each
        // HashSet is seeded independently — which would otherwise make
        // the printed scheme `<a, b>...` non-deterministically map
        // letters to type-var slots across runs.
        let mut gen_vars: Vec<TVarName> = ty_vars
            .into_iter()
            .filter(|v| !env_free_vars.contains(v) && v.is_flex())
            .collect();
        gen_vars.sort_by_key(|v| v.id());

        // Presence variables: we don't track env-bound pvars (no flow
        // makes them escape today), so we generalize every free flex
        // pvar we see. If presence-bound env entries ever exist, this
        // would need an env_free_pvars analogue.
        let mut gen_pvars: Vec<crate::types::PVarName> = pvars
            .into_iter()
            .filter(|p| p.is_flex())
            .collect();
        gen_pvars.sort_by_key(|p| p.id());

        if gen_vars.is_empty() && gen_pvars.is_empty() {
            TypeScheme::mono(ty)
        } else {
            // Collect predicates that involve the generalized variables
            let gen_var_set: std::collections::HashSet<_> = gen_vars.iter().cloned().collect();
            let mut scheme_preds = Vec::new();
            let mut remaining_constraints = Vec::new();

            for constraint in std::mem::take(&mut self.pending_constraints) {
                let pred = self.apply_subst_pred(&constraint.pred);
                let pred_vars = pred.free_vars();

                // If the predicate involves any generalized variable, include it in the scheme
                if pred_vars.iter().any(|v| gen_var_set.contains(v)) {
                    scheme_preds.push(pred);
                } else {
                    remaining_constraints.push(constraint);
                }
            }
            self.pending_constraints = remaining_constraints;

            TypeScheme::qualified_with_presence(gen_vars, gen_pvars, scheme_preds, ty)
        }
    }

    /// Apply substitution to a predicate.
    ///
    /// Reads through `main_subst` rather than `zonk` because this
    /// runs from a `&self` context (the type-class solver holds an
    /// immutable borrow of the constraint list across the call). The
    /// mirror keeps both views equivalent; correctness is identical.
    /// Migrating this off `main_subst` is a follow-up that requires
    /// restructuring the solver loop.
    fn apply_subst_pred(&self, pred: &TypePred) -> TypePred {
        TypePred {
            class: pred.class.clone(),
            types: pred.types.iter().map(|t| self.apply_subst(t)).collect(),
        }
    }

    /// Check if a type variable occurs in a type (occurs check).
    pub fn occurs_in(&self, var: TVarId, ty: &Type) -> bool {
        let ty = self.apply_subst(ty);
        self.occurs_in_impl(var, &ty)
    }

    fn occurs_in_impl(&self, var: TVarId, ty: &Type) -> bool {
        match ty {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::Error => false,

            Type::Var(TVarName::Flex(id)) => *id == var,
            Type::Var(TVarName::Skolem(_)) => false,

            Type::Func {
                this_type,
                params,
                ret,
            } => {
                this_type
                    .as_ref()
                    .map_or(false, |t| self.occurs_in_impl(var, t))
                    || params.iter().any(|p| self.occurs_in_impl(var, p))
                    || self.occurs_in_impl(var, ret)
            }

            Type::Row(row) => {
                row.props.values().any(|e| self.occurs_in_impl(var, &e.ty))
                    || matches!(&row.tail, RowTail::Open(TVarName::Flex(id)) if *id == var)
                    || matches!(&row.tail, RowTail::Recursive(_, args) if args.iter().any(|a| self.occurs_in_impl(var, a)))
            }

            Type::Array(elem) => self.occurs_in_impl(var, elem),
            Type::Promise(inner) => self.occurs_in_impl(var, inner),
            Type::Map(value) => self.occurs_in_impl(var, value),

            Type::Named(_, args) => args.iter().any(|a| self.occurs_in_impl(var, a)),

            Type::Literal(_) => false,
            Type::Union(members) => members.iter().any(|m| self.occurs_in_impl(var, m)),

            Type::Module(m) => {
                // A module's exports are schemes; the occurs check looks
                // at free variables of each scheme (i.e. those not bound
                // by the scheme's quantifier).
                m.exports
                    .values()
                    .any(|scheme| scheme.free_vars().contains(&TVarName::Flex(var)))
            }
        }
    }

    /// Check if a type variable occurs within a row type (for recursive type detection).
    /// Returns true if the variable occurs at the tail position of a row.
    pub fn is_inside_row_type(&self, var: TVarId, ty: &Type) -> bool {
        let ty = self.apply_subst(ty);
        self.is_inside_row_type_impl(var, &ty, false)
    }

    fn is_inside_row_type_impl(&self, var: TVarId, ty: &Type, in_row: bool) -> bool {
        match ty {
            Type::Row(row) => {
                // Check if var is the row tail
                if matches!(&row.tail, RowTail::Open(TVarName::Flex(id)) if *id == var) {
                    return true;
                }

                // Check inside properties - we're now inside a row
                row.props
                    .values()
                    .any(|e| self.is_inside_row_type_impl(var, &e.ty, true))
            }

            Type::Func {
                this_type,
                params,
                ret,
            } => {
                // Function's 'this' parameter can create recursive types when inside rows
                // (this is the key for equi-recursive types with object methods)
                this_type
                    .as_ref()
                    .map_or(false, |t| self.is_inside_row_type_impl(var, t, in_row))
                    || params
                        .iter()
                        .any(|p| self.is_inside_row_type_impl(var, p, in_row))
                    || self.is_inside_row_type_impl(var, ret, in_row)
            }

            Type::Var(TVarName::Flex(id)) if *id == var => {
                // Found the variable we're looking for
                // This is valid for recursion if we're inside a row
                in_row
            }

            Type::Array(elem) => self.is_inside_row_type_impl(var, elem, in_row),
            Type::Promise(inner) => self.is_inside_row_type_impl(var, inner, in_row),
            Type::Map(value) => self.is_inside_row_type_impl(var, value, in_row),

            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fresh_vars() {
        let mut state = InferState::new();

        let v1 = state.fresh_flex();
        let v2 = state.fresh_flex();
        let v3 = state.fresh_skolem();

        assert!(v1.is_flex());
        assert!(v2.is_flex());
        assert!(v3.is_skolem());
        assert_ne!(v1.id(), v2.id());
    }

    #[test]
    fn test_instantiate_mono() {
        let mut state = InferState::new();
        let scheme = TypeScheme::mono(Type::Number);
        let ty = state.instantiate(&scheme);
        assert_eq!(ty, Type::Number);
    }

    #[test]
    fn test_instantiate_poly() {
        let mut state = InferState::new();
        let scheme = TypeScheme::poly(
            vec![TVarName::Flex(100)],
            Type::simple_func(vec![Type::flex(100)], Type::flex(100)),
        );

        let ty = state.instantiate(&scheme);

        // Should be a function with fresh variables
        assert!(ty.is_func());
    }

    #[test]
    fn test_occurs_check() {
        let state = InferState::new();

        // var 0 occurs in (a0 -> a0)
        let func = Type::simple_func(vec![Type::flex(0)], Type::flex(0));
        assert!(state.occurs_in(0, &func));

        // var 1 does not occur in (a0 -> a0)
        assert!(!state.occurs_in(1, &func));

        // var 0 does not occur in Number
        assert!(!state.occurs_in(0, &Type::Number));
    }

    #[test]
    fn test_join_equal_types() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let r = state.join(span, &Type::Number, &Type::Number);
        assert_eq!(r, Type::Number);
    }

    #[test]
    fn test_join_unifiable_types() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let v = Type::flex(0);
        // a flex var joined with Number unifies to Number
        let r = state.join(span, &v, &Type::Number);
        assert_eq!(r, Type::Number);
    }

    #[test]
    fn test_join_disjoint_primitives_yields_union() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let r = state.join(span, &Type::Number, &Type::String);
        match r {
            Type::Union(members) => {
                assert_eq!(members.len(), 2);
                assert!(members.contains(&Type::Number));
                assert!(members.contains(&Type::String));
            }
            other => panic!("expected union, got {:?}", other),
        }
    }

    #[test]
    fn test_join_literal_with_base_collapses() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let r = state.join(span, &Type::lit_string("a"), &Type::String);
        assert_eq!(r, Type::String);
    }

    #[test]
    fn test_join_literals_keep_distinct() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let r = state.join(span, &Type::lit_string("a"), &Type::lit_string("b"));
        match r {
            Type::Union(m) => assert_eq!(m.len(), 2),
            other => panic!("expected union, got {:?}", other),
        }
    }

    #[test]
    fn test_join_does_not_leak_subst_on_failure() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        // join Number ~ String: unification fails, substitution must be unchanged.
        let _ = state.join(span, &Type::Number, &Type::String);
        assert!(state.main_subst.is_empty());
    }

    #[test]
    fn test_skolemize() {
        let mut state = InferState::new();
        let scheme = TypeScheme::poly(vec![TVarName::Flex(0)], Type::flex(0));

        let (skolems, ty) = state.skolemize(&scheme);

        assert_eq!(skolems.len(), 1);
        assert!(skolems[0].is_skolem());
        assert!(ty.is_var());
    }
}
