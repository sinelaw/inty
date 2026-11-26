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
            params: params
                .iter()
                .map(|p| crate::types::FuncParam {
                    presence: p.presence.clone(),
                    ty: structural_norm(&p.ty),
                    name: p.name.clone(),
                })
                .collect(),
            ret: Box::new(structural_norm(ret)),
        },
        Type::Row(row) => Type::Row(crate::types::RowType {
            props: row
                .props
                .iter()
                .map(|(k, e)| {
                    (
                        k.clone(),
                        // Normalise each presence to either Pre/Abs or a
                        // single canonical Var so the probe doesn't fire
                        // on differently-named presence vars.
                        e.map(
                            &mut |p| match p {
                                crate::types::Presence::Var(_) => {
                                    crate::types::Presence::Var(crate::types::PVarName::Flex(0))
                                }
                                other => other.clone(),
                            },
                            structural_norm(&e.ty),
                        ),
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
        Type::Maybe(z, elem) => Type::Maybe(*z, Box::new(structural_norm(elem))),
        Type::Promise(inner) => Type::Promise(Box::new(structural_norm(inner))),
        Type::Map(value) => Type::Map(Box::new(structural_norm(value))),
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(structural_norm).collect()),
        Type::Named(id, args) => Type::Named(*id, args.iter().map(structural_norm).collect()),
        Type::Union(members) => Type::Union(members.iter().map(structural_norm).collect()),
        other => other.clone(),
    }
}
use crate::error::{IntyError, LocatedError, SourceFile, TypeOrigin};
use crate::span::Span;
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
#[derive(Debug, Clone, PartialEq)]
pub struct PendingConstraint {
    pub pred: TypePred,
    pub span: Span,
}

/// How long checking one top-level declaration took (`--timings`): a
/// statement, or a group of (mutually recursive) function declarations.
#[derive(Debug, Clone)]
pub struct DeclTiming {
    /// `function f`, `const a, b`, … or `statement`.
    pub name: String,
    /// Where it is (a `SourceMap` span for an imported module's).
    pub span: Span,
    pub time: std::time::Duration,
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

/// For each use of a polymorphic binding (keyed by its span), how its
/// quantified variables were instantiated.
pub type Instantiations = HashMap<(usize, usize), Vec<(TVarName, Type)>>;

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

    /// The container of the computed member inferred last
    /// (`infer_computed_member`), so an assignment to `c[i]` can require
    /// `c` to take stores (`IndexWrite`).
    pub(crate) last_index_container: Option<Type>,
    /// The receiver of the member inferred last (`infer_member`), so an
    /// assignment to `r.p` can require `r` to take stores (`FieldWrite`).
    pub(crate) last_member_receiver: Option<Type>,
    /// The rigid variables `catch (e)` gives a caught exception, for the
    /// diagnostic when one is used at a concrete type.
    pub(crate) caught_exceptions: std::collections::HashSet<crate::types::TVarId>,
    /// Whether member reads record `last_member_receiver` and
    /// `last_index_container` (while a store's target is checked).
    pub(crate) recording_member_receiver: bool,
    /// Named types whose body has no variable but its parameters (most
    /// declared ones): nothing in them is fixed by an environment that
    /// reaches them, so `env_fixed_vars` needn't resolve them again.
    pub(crate) closed_named: std::collections::HashSet<TypeId>,

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

    /// Synthesised type of every expression, keyed by the expression's
    /// `(span.start, span.end)`. `None` (the default) records nothing;
    /// set it to `Some(HashMap::new())` before inference to opt in.
    /// Types are stored unsubstituted — read them through
    /// [`Self::flatten_type`] after inference completes. Used by code
    /// generators that need a type for every node, not just bindings.
    pub expr_types: Option<HashMap<(usize, usize), Type>>,

    /// How each reference to a polymorphic binding was instantiated,
    /// keyed by the identifier's `(span.start, span.end)`: the scheme's
    /// quantified variables paired with the fresh types that replaced
    /// them at that use. `None` (the default) records nothing. Together
    /// with [`Self::expr_types`] this lets a code generator monomorphise
    /// — emit one copy of a polymorphic function per concrete
    /// instantiation — without re-running inference.
    pub instantiations: Option<Instantiations>,

    /// Type origins for error reporting.
    pub type_origins: HashMap<TVarName, TypeOrigin>,
    /// The variables of `type_origins` with an origin that makes a
    /// function a method ([`TypeOrigin::makes_method`]: a call that
    /// passes its object as `this`, a body that reads `this`) whose
    /// class may still be bound to a recursive type: see
    /// [`Self::method_origins`].
    pub(crate) method_origin_vars: Vec<crate::types::TVarId>,
    /// For a recursive type made when a function's `this` was bound to
    /// its object (`create_recursive_type`): what made the function a
    /// method. A generalised type keeps the recursive type, not the
    /// variables the origins are recorded on.
    pub(crate) rec_origins: HashMap<crate::types::TypeId, Vec<TypeOrigin>>,
    /// The fields a property read added to an open record (`o.name`, with
    /// `o` of a type not known yet): the tail the record had then, the
    /// field, and the read. A generalised record keeps its tail, not the
    /// variable the field's origin is on: see [`Self::row_member_origin`].
    pub(crate) row_field_origins: Vec<(crate::types::TVarId, String, TypeOrigin)>,
    /// The fields of the object literals `const`s are bound to: each
    /// field's path (`a.b` for a field of a nested literal), its span,
    /// and, for a function, whether it reads `this`. A mismatch in a
    /// member of a value passed by name points at the field.
    pub(crate) literal_fields:
        HashMap<crate::ast::resolve::BindingId, std::sync::Arc<Vec<LiteralField>>>,

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

    /// The environment a program left behind when its inference
    /// collected errors: `infer_program*` then returns the first error
    /// and drops the env, though recovery (failed bindings bound to
    /// `Type::Error`) built one for every statement. Set by
    /// `infer_program_with_env` on that path; read it with
    /// [`InferState::take_env_after_errors`].
    pub(in crate::infer) env_after_errors: Option<crate::infer::TypeEnv>,

    /// Parallel to `errors`: the source file each error's span indexes
    /// into, or `None` for the entry source. Kept in lockstep with
    /// `errors` through `push_error` / `take_errors`, so a diagnostic
    /// raised while checking an imported module renders against that
    /// module rather than the entry file.
    error_sources: Vec<Option<SourceFile>>,

    /// The source file errors are currently attributed to. Set by the
    /// module loader while inferring an imported module and restored
    /// afterwards; `None` means the entry source.
    current_source: Option<SourceFile>,
    /// The span ranges of imported modules (see `SourceMap`).
    pub sources: crate::error::SourceMap,
    /// Nesting of [`Self::quietly`]: while positive, a failed unification
    /// is being speculated and its error will be discarded.
    pub(crate) quiet: u32,
    /// How many imported modules are being checked (nested).
    pub module_depth: usize,
    /// `--timings`: when `Some`, the time each top-level declaration of
    /// every program took (see [`DeclTiming`]).
    pub timings: Option<Vec<DeclTiming>>,
    /// `--timings`: each module's own checking time (its imports
    /// excluded), in the order they finished.
    pub module_timings: Vec<(String, std::time::Duration)>,
    /// Nesting of `infer_stmt_list` within the current program: 1 is its
    /// top level.
    pub(in crate::infer) stmt_list_depth: usize,
    /// Time top-level function groups took while a top-level statement
    /// was being checked (so the statement's own time excludes them).
    pub(in crate::infer) timing_nested: std::time::Duration,
    /// Modules checked so far this run, by canonical path: their
    /// environments and export tables (see `modules::load_imported`).
    pub module_cache:
        HashMap<std::path::PathBuf, (crate::infer::TypeEnv, crate::modules::ExportTable)>,
    /// Modules that failed this run, by canonical path: reported once,
    /// and not checked again by a later importer (see
    /// `modules::resolve_imports`).
    pub failed_modules: std::collections::HashSet<std::path::PathBuf>,
    /// The environment each project's libs were loaded into this run, by
    /// its canonical `inty.json` path (see `modules::with_project_libs`).
    pub project_libs: HashMap<std::path::PathBuf, crate::infer::TypeEnv>,

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

    /// Names of factory functions a frontend lowered a `class` to and
    /// which should be branded nominally (from `Program::class_brands`).
    /// When a function decl in this set is generalised, its inferred
    /// return row is wrapped in a fresh brand. Empty unless a frontend
    /// emits nominal classes.
    pub class_brand_names: std::collections::HashSet<String>,

    /// Brand ids minted for each nominal class, keyed by class name.
    /// Populated as factories are branded; lets `isinstance`-style
    /// checks map a class name back to its brand. See
    /// `docs/pyi-import-mapping.md` §8.
    pub class_brand_ids: HashMap<String, TypeId>,
    /// The `switch` statements that always take some case: those with a
    /// `default`, and those whose cases cover every value of a finite
    /// discriminant. `definitely_returns` reads it once a body is inferred.
    pub exhaustive_switches: std::collections::HashSet<crate::span::Span>,
    /// Set just before a member of an object literal or class (a method,
    /// a getter, a field holding a function literal) is inferred, and taken
    /// by that function's body: what never completes there returns `never`,
    /// not a type variable, as the object's type holds the member
    /// monomorphically (each use would otherwise fix it).
    pub(crate) member_function: bool,
    /// Set just before a method with an annotation is inferred, and taken
    /// by it: the annotation's type is called with the method's own
    /// `this` unless it says (`this: T`), as a TypeScript method
    /// signature is, where a function's annotation without `this:` says
    /// the function uses none.
    pub(crate) annotated_method: bool,
    /// The spans of the factory functions `class` declarations lowered to
    /// (`Program::class_decls`): typed where they stand, not hoisted.
    pub class_decls: std::collections::HashSet<crate::span::Span>,
    /// Brand ids allocated for a program's classes before its aliases
    /// are parsed (see `infer_program_with_env`), taken by the class's
    /// factory when it is branded.
    pub reserved_class_ids: HashMap<String, TypeId>,
    /// `then` / `catch` callback results waiting for their call to
    /// settle them: `(callback result, promised value)`. See
    /// `builtins::promise_method_type`.
    pub(crate) promise_results: Vec<(Type, Type)>,
    /// The `this` of a callee called detached (`f()`) that wasn't known
    /// at the call, with the call's span and the callee's name: settled
    /// when it is (`settle_detached`), at the latest as `Undefined`.
    pub(crate) pending_detached: Vec<(Type, Span, String)>,
    /// The `this` of a callee called as a method (`o.f()`) that wasn't
    /// known at the call, with the receiver and the call's span: settled
    /// when it is (`settle_receivers`), at the latest as a function that
    /// uses no `this`, or a method of the receiver (`PendingReceiver`).
    pub(crate) pending_receivers: Vec<PendingReceiver>,
    /// The `this` variables of functions whose bodies mention `this`
    /// (methods, by the rule that a body says whether a function is
    /// one): see `settle_receivers`.
    pub(crate) method_this_vars: Vec<crate::types::TVarId>,
    /// An `async` body's `return e` whose type wasn't known at the
    /// `return`, and what it gives the promise: settled when it is
    /// (`settle_async_returns`), at the latest as a value that isn't a
    /// promise.
    pub(crate) pending_async_returns: Vec<(Type, Type, Span)>,
    /// Parameters with an undecided presence (declared optional) that a
    /// call filled (`true`) or skipped (`false`) without deciding them
    /// (`fill_optional_params`): settled by `settle_optional_params`.
    pub(crate) pending_optional_params: Vec<(crate::types::PVarName, bool, Span)>,
    /// Which declaration each identifier refers to, and which bindings
    /// are never written after their initialiser: the only ones
    /// narrowing refines (see `ast::resolve`).
    pub resolution: crate::ast::resolve::Resolution,
    /// Every program-declared binding's scheme as last declared, by
    /// declaration: where a read finds a binding the environment it's
    /// checked in doesn't hold (a `var` declared in a block, a use
    /// before the declaration).
    pub(in crate::infer) local_types: HashMap<crate::ast::resolve::BindingId, TypeScheme>,
    /// Bindings read before any declaration of them was checked: the
    /// fresh type the read got, which the declaration unifies with, and
    /// where the first read was.
    /// The bindings that are declarations without a value (`const X;`
    /// under an annotation, an external `class X;`): the only bases an
    /// external class may extend.
    pub(in crate::infer) ambient: std::collections::HashSet<crate::infer::env::Key>,
    pub(in crate::infer) forward_locals:
        HashMap<crate::ast::resolve::BindingId, (Type, String, Span)>,
    /// Bindings some read found only in `local_types`. The environment
    /// doesn't show them to generalisation, so their variables are held
    /// fixed there explicitly.
    pub(in crate::infer) escaped_locals: std::collections::HashSet<crate::ast::resolve::BindingId>,
    /// Where each binding was first declared. Another declaration of the
    /// same binding (`var x` twice, `for (var x of …)`, a Lua `function
    /// f` assigning a local) must agree with it: one binding, one type.
    pub(in crate::infer) local_decl_spans: HashMap<crate::ast::resolve::BindingId, Span>,

    /// The lexical environment in scope while a type annotation is being
    /// lowered, used to resolve a class-name `TypeAst::Ref` to the class's
    /// actual type *by scope* — a bare name binds in this env, a qualified
    /// `mod.Class` resolves through the `mod` module namespace. Set by
    /// [`InferState::lower_type_ast_in_env`] for the duration of one
    /// annotation; `None` elsewhere (refs then fall back to opaque).
    pub(in crate::infer) annotation_env: Option<crate::infer::TypeEnv>,

    /// Span of the annotation currently being lowered, used to attach a
    /// `TypeError::UnknownTypeRef` to the right source range when a
    /// `TypeAst::Ref` doesn't resolve. Set by the span-aware lowering
    /// entry points (e.g. `lower_type_ast_in_env_with_span`); `None`
    /// elsewhere, in which case an unresolved ref is silently degraded
    /// to opaque (the stub-reading contract: typeshed and other stubs
    /// have unmodelled types we don't want to nag about).
    pub(in crate::infer) current_annotation_span: Option<crate::span::Span>,

    /// Stack of `return`-value accumulators, one frame per function body
    /// currently being inferred (innermost on top). Each `return <e>`
    /// pushes `e`'s type onto the top frame; the function's return type is
    /// then the join of its collected returns plus `Undefined` when control
    /// can fall off the end (a Python procedure / JS function with no
    /// trailing `return` yields `None`/`undefined`). See
    /// `infer_function_with_this`.
    pub(in crate::infer) return_value_stack: Vec<Vec<Type>>,
    /// Per return frame, the annotated return type `return`s are
    /// checked against (instead of being joined), if there is one.
    pub(in crate::infer) return_expected_stack: Vec<Option<Type>>,
    /// Bumped wherever pending constraints are removed (solving,
    /// generalising), to check that no speculative branch does.
    pub(crate) constraint_removals: u64,

    /// The type a function returns when it falls off the end (no explicit
    /// `return`): JS `undefined` (`Type::Undefined`) by default, or
    /// `Type::Null` for languages whose unit value is null (Python `None`,
    /// Lua `nil`). Derived from `Program::language` at the start of
    /// `infer_program_with_env`.
    pub(in crate::infer) unit_type: Type,

    /// The source language of the program being inferred. Drives the few
    /// frontend-specific rules — currently the unit type and which
    /// primitive-method surface (`str`/`list` vs `String`/`Array`) a value
    /// carries. Defaults to JavaScript.
    pub(crate) language: crate::ast::SourceLanguage,

    /// Coinductive unification assumptions for recursive `Named` types.
    /// When `unify` is about to unfold a `Named(id, ...)` against another
    /// type during structural recursion, the (id, kind) pair is pushed
    /// here. If the same pair recurs deeper in the same `unify` call —
    /// e.g. two distinct equirecursive types of the same shape, or a
    /// nominal type whose instance row transitively mentions itself —
    /// the recursive arm succeeds by coinduction (Brandt-Henglein 1998;
    /// Pierce, TAPL ch. 21). Without this, equirecursive types of
    /// distinct ids unroll forever. The stack is logically scoped to a
    /// single `unify` invocation but lives on the state so it threads
    /// through `&mut self` without rewriting the call signature.
    pub(in crate::infer) unfold_assumptions: Vec<UnfoldAssumption>,
    /// Current nesting of [`Self::unify`] (0: no unification under way).
    pub(in crate::infer) unify_depth: usize,
    /// The properties [`Self::unify`] is inside, outermost first: the
    /// field of a record it is comparing, and the field of that, … A
    /// mismatch deep in two large types (a class's instance against what
    /// its uses expect of it) is reported at the span of the whole
    /// comparison; the path says which member it is.
    pub(in crate::infer) unify_path: Vec<String>,
    /// Pairs of variables, each bound to a type, that the outermost
    /// [`Self::unify`] under way has unified (or is unifying): a pair met
    /// again is taken as unified (coinductively, as for recursive types).
    /// Two bound variables' types are compared, not linked, so without
    /// this a type that mentions them in many places (an element's row:
    /// each of its handlers' events mentions the element) is compared
    /// again at each, which is exponential in how deeply such types nest.
    pub(in crate::infer) unify_bound_pairs: std::collections::HashSet<(TVarId, TVarId)>,
    /// The pairs of [`Self::unify_bound_pairs`] the outermost
    /// unification under way has unified: linked when it succeeds
    /// (`link_bound`).
    pub(in crate::infer) unified_bound_pairs: Vec<(TVarId, TVarId)>,
    /// Whether the outermost unification under way went through an arm
    /// that accepts two types that aren't equal (see `link_bound`).
    pub(in crate::infer) unify_inexact: bool,
    /// The type of the value each plain `x = e` assigned, by where its
    /// `x` is: what narrowing knows about a binding written once
    /// (`resolve::Resolution::sole_write_at`) after that write.
    pub(in crate::infer) assigned_values: HashMap<(usize, usize), Type>,
}

/// One in-progress unfold the unifier is mid-recursion on. Two
/// equirecursive types with distinct ids alternate-unrolling forever
/// without this; with it, re-entering an assumption signals the cycle
/// has closed and the unification is sound by coinduction.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(in crate::infer) enum UnfoldAssumption {
    /// `Named(id_a, args_a) ↔ Named(id_b, args_b)` unfold in progress
    /// (smaller id first), arguments included.
    NamedPair(TypeId, Vec<Type>, TypeId, Vec<Type>),
    /// `Named(id, args) ↔ other` unfold in progress, with both sides as
    /// they were (zonked) when the unfold began. Only the *same* goal
    /// recurring closes the cycle: keying by the id alone let
    /// `μt. Number → t` meet `Number → Number → Number`, succeed on the
    /// first unfold's assumption one level down, and accept a function
    /// whose second call returns a function as one returning a number.
    NamedRow(TypeId, Vec<Type>, Type),
    /// A recursive type `Named(id, args)` and the variable (its root)
    /// bound to the type it is being unified with. The variable is the
    /// node: met again, by whatever type it has been bound to since (a
    /// row extended with fresh tails), it is the same goal.
    VarNamed(TVarId, TypeId, Vec<Type>),
}

/// State captured by [`InferState::snapshot_inference`] and consumed
/// by [`InferState::restore_snapshot`]. Crate-private so the
/// snapshot/restore pair is the only way to use it.
#[derive(Debug, Clone)]
pub(crate) struct InferSnapshot {
    pub(crate) subst: crate::types::subst::SubstMark,
    /// How many constraints were pending: a speculative branch only
    /// adds to them, so rolling back truncates.
    pub(crate) constraints: usize,
    /// `constraint_removals` at the snapshot, to check that claim.
    pub(crate) constraint_removals: u64,
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
    /// When `Some(id)`, this alias is a declared *nominal* type:
    /// references resolve to `Type::Named(id, args)` (brand identity)
    /// instead of inlining `body`. `body` is then the representation
    /// the brand wraps. `None` for ordinary structural aliases.
    pub nominal_id: Option<crate::types::TypeId>,
    /// When `Some(id)`, a structural alias that refers to itself
    /// (directly or through other aliases): references resolve to the
    /// equi-recursive `Type::Named(id, args)`, whose definition (the
    /// body) is registered in the named-type table — transparent, unlike
    /// a nominal brand.
    pub rec_id: Option<crate::types::TypeId>,
    /// A class name reserved before its class is inferred (so aliases
    /// declared in the same file can name it): the brand's type
    /// parameters aren't known yet, so any number of arguments is
    /// accepted.
    pub open_arity: bool,
    /// A JavaScript class's instance type (the brand of its factory):
    /// its parameters are the types its constructor and methods leave
    /// generic.
    pub class: bool,
}

impl Default for InferState {
    fn default() -> Self {
        Self::new()
    }
}

/// The largest type (in nodes, written out) a binding is generalised at.
/// A scheme holds its type written out, as a tree: a type that nests
/// types mentioning each other many times (an element whose fields
/// mention the element it was appended to, and so on) is exponentially
/// larger than the substitution it is in. One larger than this keeps its
/// monomorphic type.
pub(crate) const MAX_GENERALISED: usize = 200_000;

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
            main_subst: Subst::with_trail(),
            var_table: VarTable::new(),
            named_types: HashMap::new(),
            type_id_source: 0,
            type_classes: HashMap::new(),
            pending_constraints: Vec::new(),
            last_index_container: None,
            last_member_receiver: None,
            caught_exceptions: std::collections::HashSet::new(),
            recording_member_receiver: false,
            closed_named: std::collections::HashSet::new(),
            decl_types: HashMap::new(),
            decl_schemes: HashMap::new(),
            expr_types: None,
            instantiations: None,
            type_origins: HashMap::new(),
            method_origin_vars: Vec::new(),
            rec_origins: HashMap::new(),
            row_field_origins: Vec::new(),
            literal_fields: HashMap::new(),
            warnings: Vec::new(),
            errors: Vec::new(),
            env_after_errors: None,
            error_sources: Vec::new(),
            current_source: None,
            sources: Default::default(),
            module_depth: 0,
            quiet: 0,
            module_cache: HashMap::new(),
            failed_modules: std::collections::HashSet::new(),
            project_libs: HashMap::new(),
            timings: None,
            module_timings: Vec::new(),
            stmt_list_depth: 0,
            timing_nested: std::time::Duration::ZERO,
            config,
            type_aliases: HashMap::new(),
            class_brand_names: std::collections::HashSet::new(),
            class_brand_ids: HashMap::new(),
            exhaustive_switches: std::collections::HashSet::new(),
            member_function: false,
            annotated_method: false,
            class_decls: std::collections::HashSet::new(),
            reserved_class_ids: HashMap::new(),
            promise_results: Vec::new(),
            pending_detached: Vec::new(),
            pending_receivers: Vec::new(),
            method_this_vars: Vec::new(),
            pending_async_returns: Vec::new(),
            pending_optional_params: Vec::new(),
            resolution: Default::default(),
            local_types: HashMap::new(),
            forward_locals: HashMap::new(),
            ambient: std::collections::HashSet::new(),
            escaped_locals: Default::default(),
            local_decl_spans: HashMap::new(),
            annotation_env: None,
            current_annotation_span: None,
            return_value_stack: Vec::new(),
            return_expected_stack: Vec::new(),
            constraint_removals: 0,
            unit_type: Type::Undefined,
            language: crate::ast::SourceLanguage::JavaScript,
            unfold_assumptions: Vec::new(),
            unify_depth: 0,
            unify_path: Vec::new(),
            unify_bound_pairs: std::collections::HashSet::new(),
            unified_bound_pairs: Vec::new(),
            unify_inexact: false,
            assigned_values: HashMap::new(),
        }
    }

    /// Set the source language and derive the unit / "no value" type.
    /// `infer_program_with_env` does this from `Program::language`; callers
    /// that infer statements directly (without a `Program`) use this.
    pub fn set_language(&mut self, language: crate::ast::SourceLanguage) {
        self.language = language;
        self.unit_type = if language.unit_is_null() {
            Type::Null
        } else {
            Type::Undefined
        };
    }

    /// Record an inference error and continue. Used by `infer_stmt_list`
    /// when `Type::Error` recovery lets us keep type-checking past a
    /// failing statement. The first call's error is what the public
    /// `infer_program*` API returns via `Err`; later errors are only
    /// visible to callers that drain `errors` after the run.
    /// An annotation as parsed, or, when it doesn't parse, `None` with
    /// the error reported: what it annotates is then checked as if it
    /// had no annotation, rather than given up on (its body, and what
    /// uses it, still typed).
    pub(in crate::infer) fn annotation_or_report<T>(
        &mut self,
        parsed: crate::infer::type_parser::ParseResult<T>,
    ) -> Option<T> {
        match parsed {
            Ok(t) => Some(t),
            Err(e) => {
                self.push_error(e.into());
                None
            }
        }
    }

    pub fn push_error(&mut self, err: IntyError) {
        // Reported: render the types it holds.
        let err = self.render_error(err);
        // A statement list re-raises the first error it recorded (see
        // `infer_stmt_list`), and the recovery around it (a function
        // group, an enclosing statement) records what it catches: keep
        // one. Spans are distinct across modules, so an equal error is
        // the same diagnostic.
        let shown = format!("{err:?}");
        if self.errors.iter().any(|e| format!("{e:?}") == shown) {
            return;
        }
        self.errors.push(err);
        self.error_sources.push(self.current_source.clone());
    }

    /// After an `infer_program*` call returned an error, the environment
    /// the program would otherwise have returned: every top-level
    /// binding with its inferred type, the ones whose statements failed
    /// bound to `Type::Error`. Lets an editor keep answering hover and
    /// completion queries in a file that has a type error somewhere.
    /// `None` when the last program inferred cleanly.
    pub fn take_env_after_errors(&mut self) -> Option<crate::infer::TypeEnv> {
        self.env_after_errors.take()
    }

    /// Drain accumulated errors, leaving the state empty. The CLI calls
    /// this after `infer_program_with_env` to report every error,
    /// not just the first.
    pub fn take_errors(&mut self) -> Vec<IntyError> {
        self.error_sources.clear();
        std::mem::take(&mut self.errors)
    }

    /// Like `take_errors`, but pairs each error with the source file its
    /// span indexes into (`None` = the entry source). Lets the CLI render
    /// an imported module's diagnostics against that module's file rather
    /// than the entry source.
    pub fn take_located_errors(&mut self) -> Vec<LocatedError> {
        let sources = std::mem::take(&mut self.error_sources);
        let errors = std::mem::take(&mut self.errors);
        errors
            .into_iter()
            .zip(sources.into_iter().chain(std::iter::repeat(None)))
            .map(|(error, source)| LocatedError { error, source })
            .collect()
    }

    /// Set the source file new errors are attributed to, returning the
    /// previous value so the caller can restore it. The module loader
    /// brackets an imported module's inference with this so the module's
    /// diagnostics carry its own source.
    pub fn set_current_source(&mut self, source: Option<SourceFile>) -> Option<SourceFile> {
        std::mem::replace(&mut self.current_source, source)
    }

    /// The source file currently attributed to new errors (`None` = entry
    /// source). Used to locate an error propagated out of import
    /// resolution (e.g. a parse failure in an imported module).
    pub fn current_source(&self) -> Option<SourceFile> {
        self.current_source.clone()
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
        if let (TVarName::Flex(id), true) = (&var, origin.makes_method()) {
            self.method_origin_vars.push(*id);
            let n = self.method_origin_vars.len();
            if n >= 4096 && n.is_power_of_two() {
                self.prune_method_origin_vars();
            }
        }
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
                .or_else(|| params.iter().find_map(|p| self.find_origin_in_type(&p.ty)))
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
            Type::Array(elem) | Type::Maybe(_, elem) => self.find_origin_in_type(elem),
            Type::Promise(inner) => self.find_origin_in_type(inner),
            Type::Map(value) => self.find_origin_in_type(value),
            Type::Tuple(elems) => elems.iter().find_map(|e| self.find_origin_in_type(e)),
            Type::Named(_, args) => args.iter().find_map(|a| self.find_origin_in_type(a)),
            Type::Union(members) => members.iter().find_map(|m| self.find_origin_in_type(m)),
            _ => None,
        }
    }

    /// The root of `id`'s class, read without compressing paths (for
    /// `&self` readers); `None` for a variable the table doesn't hold.
    fn class_root(&self, id: crate::types::TVarId) -> Option<crate::types::TVarId> {
        use super::var_table::Resolution;
        let mut cur = id;
        for _ in 0..=self.var_table.len() {
            match self.var_table.peek(cur)? {
                Resolution::Link(next) => cur = *next,
                _ => return Some(cur),
            }
        }
        None
    }

    /// The recursive type `root` is bound to, if it is bound to one.
    fn bound_rec_type(&self, root: crate::types::TVarId) -> Option<crate::types::TypeId> {
        match self.var_table.bound(root)? {
            Type::Named(id, _) => Some(*id),
            _ => None,
        }
    }

    /// What made a function whose `this` is `this` a method (see
    /// [`TypeOrigin::makes_method`]): the origins recorded on the
    /// variables unified with it, and on the recursive type it is (a
    /// method's `this` is its object, whose type holds the method).
    /// Sorted by where they are, at most [`MAX_ORIGINS`].
    pub(crate) fn method_origins(&self, this: &Type) -> Vec<TypeOrigin> {
        let (root, rec) = match this {
            Type::Var(TVarName::Flex(v)) => match self.class_root(*v) {
                Some(r) => (Some(r), self.bound_rec_type(r)),
                None => return Vec::new(),
            },
            Type::Named(id, _) => (None, Some(*id)),
            _ => return Vec::new(),
        };
        let mut out: Vec<TypeOrigin> = rec
            .and_then(|id| self.rec_origins.get(&id))
            .cloned()
            .unwrap_or_default();
        for id in &self.method_origin_vars {
            let Some(r) = self.class_root(*id) else {
                continue;
            };
            if Some(r) == root || (rec.is_some() && self.bound_rec_type(r) == rec) {
                if let Some(o) = self.type_origins.get(&TVarName::Flex(*id)) {
                    out.push(o.clone());
                }
            }
        }
        tidy_origins(&mut out);
        out
    }

    /// A recursive type `type_id` was made for the variable a function's
    /// `this` was bound to (`create_recursive_type`): it keeps what made
    /// the function a method, which a generalised type, holding the
    /// recursive type rather than the variable, would otherwise lose.
    /// `method_origin_vars` is pruned then, so it stays short.
    pub(crate) fn note_rec_origins(&mut self, type_id: crate::types::TypeId) {
        if self.method_origin_vars.is_empty() {
            return;
        }
        let origins = self.method_origins(&Type::Named(type_id, Vec::new()));
        if !origins.is_empty() {
            self.rec_origins.insert(type_id, origins);
        }
        self.prune_method_origin_vars();
    }

    /// Outside a speculative attempt (whose bindings may be undone), drop
    /// the variables no longer free from `method_origin_vars`, giving
    /// the origins of those bound to a recursive type to it.
    fn prune_method_origin_vars(&mut self) {
        if self.quiet > 0 {
            return;
        }
        let mut keep = Vec::new();
        for id in std::mem::take(&mut self.method_origin_vars) {
            let Some(root) = self.class_root(id) else {
                continue;
            };
            if self.var_table.bound(root).is_none() {
                keep.push(id);
            } else if let Some(rec) = self.bound_rec_type(root) {
                if let Some(o) = self.type_origins.get(&TVarName::Flex(id)).cloned() {
                    let list = self.rec_origins.entry(rec).or_default();
                    list.push(o);
                    tidy_origins(list);
                }
            }
        }
        self.method_origin_vars = keep;
    }

    /// A property read of `field` added it to an open record with the
    /// tail `tail` (see `row_field_origins`): record where, if the field's
    /// type `ty` has an origin.
    pub(crate) fn note_field_read(&mut self, tail: &TVarName, field: &str, ty: &Type) {
        if let (TVarName::Flex(tail), Type::Var(v)) = (tail, ty) {
            if let Some(origin) = self.type_origins.get(v).cloned() {
                self.row_field_origins
                    .push((*tail, field.to_string(), origin));
            }
        }
    }

    /// The tail a record ends in: its open tail, through the records it
    /// was extended with (`ρ := {f: T | ρ'}`); `None` for a closed one.
    fn row_end(&self, mut tail: crate::types::TVarId) -> Option<crate::types::TVarId> {
        for _ in 0..10_000 {
            let root = self.class_root(tail)?;
            match self.var_table.bound(root) {
                None => return Some(root),
                Some(Type::Row(row)) => match &row.tail {
                    RowTail::Open(TVarName::Flex(next)) => tail = *next,
                    _ => return None,
                },
                Some(_) => return None,
            }
        }
        None
    }

    /// Where the member `path` (`a.b`) of the type `whole` got its type,
    /// when a property read added it to an open record (see
    /// `row_field_origins`): the record's tail leads to `whole`'s.
    pub(crate) fn row_member_origin(&self, whole: &Type, path: &str) -> Option<TypeOrigin> {
        if self.row_field_origins.is_empty() {
            return None;
        }
        let head = |t: &Type| -> Option<Type> {
            let mut t = t.clone();
            for _ in 0..64 {
                match t {
                    Type::Var(TVarName::Flex(v)) => {
                        t = self.var_table.bound(self.class_root(v)?)?.clone()
                    }
                    Type::Named(id, ref args) if !self.is_nominal_type(id) => {
                        t = self.unroll_named(id, args)?
                    }
                    _ => return Some(t),
                }
            }
            None
        };
        let mut segments: Vec<&str> = path.split('.').collect();
        let last = segments.pop()?;
        let mut ty = head(whole)?;
        for seg in segments {
            let Type::Row(row) = &ty else { return None };
            ty = head(&row.props.get(&crate::types::PropName(seg.to_string()))?.ty)?;
        }
        let Type::Row(row) = &ty else { return None };
        let RowTail::Open(TVarName::Flex(tail)) = &row.tail else {
            return None;
        };
        let end = self.row_end(*tail)?;
        self.row_field_origins
            .iter()
            .find(|(start, field, _)| field == last && self.row_end(*start) == Some(end))
            .map(|(_, _, origin)| origin.clone())
    }

    /// The field of the value `arg` (an object literal, or a `const`
    /// bound to one) at the member path `path`, or the innermost one
    /// enclosing it.
    pub(crate) fn literal_field(&self, arg: &crate::ast::Expr, path: &str) -> Option<LiteralField> {
        let found;
        let fields: &[LiteralField] = match arg {
            crate::ast::Expr::Object { properties, .. } => {
                let mut out = Vec::new();
                collect_literal_fields(properties, "", &mut out);
                found = out;
                &found
            }
            crate::ast::Expr::Ident { name, span } => match self.key_of(*span, name) {
                crate::infer::env::Key::Local(id) => self.literal_fields.get(&id)?,
                crate::infer::env::Key::Name(_) => return None,
            },
            _ => return None,
        };
        let encloses = |f: &&LiteralField| {
            path == f.path
                || path
                    .strip_prefix(f.path.as_str())
                    .is_some_and(|rest| rest.starts_with('.'))
        };
        let field = fields
            .iter()
            .filter(encloses)
            .max_by_key(|f| f.path.len())?;
        let mut field = field.clone();
        if field.path != path {
            // A function's `this` is about the field itself only.
            field.reads_this = None;
        }
        Some(field)
    }

    /// Record the fields of the object literal `init` the binding
    /// declared at `span` as `name` is bound to (see `literal_fields`).
    pub(crate) fn record_literal_fields(
        &mut self,
        span: Span,
        name: &str,
        init: &crate::ast::Expr,
    ) {
        let crate::ast::Expr::Object { properties, .. } = init else {
            return;
        };
        if let crate::infer::env::Key::Local(id) = self.key_of(span, name) {
            let mut fields = Vec::new();
            collect_literal_fields(properties, "", &mut fields);
            self.literal_fields.insert(id, std::sync::Arc::new(fields));
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
        debug_assert_eq!(id, self.name_source, "var_table id must match name_source");
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
        debug_assert_eq!(id, self.name_source, "var_table id must match name_source");
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

    /// [`Self::callable_row_open`] for a static function with explicit
    /// parameters (some optional).
    pub fn callable_row_open_with_params(
        &mut self,
        params: Vec<crate::types::FuncParam>,
        ret: Type,
    ) -> Type {
        use crate::types::{PropName, RowType, CALLABLE_KEY};
        let func = Type::raw_func_with_params(None, params, ret);
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

    /// `ty` with its head resolved through the substitution (what a
    /// bound variable stands for), and nothing below it: cheap on a large
    /// type, where [`Self::zonk`] copies the whole of it.
    pub fn zonk_head(&mut self, ty: &Type) -> Type {
        super::zonk::zonk_head_cow(&mut self.var_table, ty).into_owned()
    }

    /// [`Self::zonk_head`] of a type the caller gives up: one that is
    /// already a head is returned as is, not copied.
    pub fn zonk_head_into(&mut self, ty: Type) -> Type {
        match ty {
            Type::Var(_) => self.zonk_head(&ty),
            head => head,
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

    /// Whether `t`'s resolved head satisfies `f`, without resolving (or
    /// copying) anything below the head.
    pub fn head_is(&mut self, t: &Type, f: impl FnOnce(&Type) -> bool) -> bool {
        super::zonk::with_head(&mut self.var_table, t, f)
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
    ///
    /// Nothing is copied: the substitution and the var table keep undo
    /// trails, pending constraints and number-kinded variables are only
    /// added to while speculating, so a restore undoes or truncates.
    /// (Cloning them made every `subsume` cost time in proportion to
    /// everything inferred so far — quadratic checking.)
    pub(crate) fn snapshot_inference(&self) -> InferSnapshot {
        InferSnapshot {
            subst: self.main_subst.mark(),
            constraints: self.pending_constraints.len(),
            constraint_removals: self.constraint_removals,
            trail: self.var_table.snapshot(),
        }
    }

    /// Run a speculative attempt whose error is discarded (the caller
    /// restores a snapshot on failure): errors raised meanwhile skip
    /// rendering their types (see `unification_error`).
    pub(crate) fn quietly<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.quiet += 1;
        let result = f(self);
        self.quiet -= 1;
        result
    }

    /// Restore a snapshot taken by [`Self::snapshot_inference`].
    pub(crate) fn restore_snapshot(&mut self, snap: InferSnapshot) {
        self.main_subst.undo_to(snap.subst);
        debug_assert_eq!(
            self.constraint_removals, snap.constraint_removals,
            "a speculative branch removed pending constraints"
        );
        self.pending_constraints.truncate(snap.constraints);
        self.var_table.restore(snap.trail);
        // A pair unified in what was undone isn't unified any more.
        self.unify_bound_pairs.clear();
        self.unified_bound_pairs.clear();
        self.unify_inexact = false;
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

    /// `ty` with its head resolved and, through a union or a sum, each
    /// arm's head: what joining and `&&`/`||` look at, without resolving
    /// (copying) the arms whole.
    pub(crate) fn zonk_arms(&mut self, ty: &Type) -> Type {
        match self.zonk_head(ty) {
            Type::Union(members) => Type::union(
                members
                    .iter()
                    .map(|m| self.zonk_arms(m))
                    .collect::<Vec<_>>(),
            ),
            Type::Maybe(_, _) => {
                let Type::Maybe(z, inner) = self.zonk_head(ty) else {
                    unreachable!("just matched")
                };
                Type::union(vec![z.ty(), self.zonk_arms(&inner)])
            }
            other => other,
        }
    }

    /// Whether `ty` written out (as a scheme holds it) would exceed
    /// [`MAX_GENERALISED`] nodes.
    pub(crate) fn too_large_to_generalise(&self, ty: &Type) -> bool {
        self.main_subst.flattened_size(ty, MAX_GENERALISED + 1) > MAX_GENERALISED
    }

    /// [`Self::too_large_to_generalise`], or a waiting constraint the
    /// generalisation of `ty` would carry in its scheme (one reaching its
    /// variables, or those of another it carries) is: `generalize` writes
    /// those out too.
    pub(crate) fn scheme_too_large(&self, ty: &Type) -> bool {
        if self.too_large_to_generalise(ty) {
            return true;
        }
        let mut reach = crate::types::subst::Reach::default();
        self.main_subst.reach(ty, &mut reach);
        let mut vars = reach.vars;
        let mut left: Vec<&PendingConstraint> = self.pending_constraints.iter().collect();
        loop {
            let mut rest = Vec::new();
            let mut took = false;
            for c in left {
                let mut r = crate::types::subst::Reach::default();
                for t in &c.pred.types {
                    self.main_subst.reach(t, &mut r);
                }
                if r.vars.iter().any(|v| v.is_flex() && vars.contains(v)) {
                    if c.pred.types.iter().any(|t| self.too_large_to_generalise(t)) {
                        return true;
                    }
                    vars.extend(r.vars);
                    took = true;
                } else {
                    rest.push(c);
                }
            }
            left = rest;
            if !took {
                return false;
            }
        }
    }

    /// How large `ty` is written out (see [`Subst::flattened_size`]),
    /// counted up to a cap well past what a printer shows.
    pub fn flattened_size(&self, ty: &Type) -> usize {
        self.main_subst.flattened_size(ty, 1 << 20)
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
                types: p.types.iter().map(|t| self.main_subst.flatten(t)).collect(),
                origin: p.origin,
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

    /// Join the types of two branches: of a conditional, the `return`s of
    /// a function, the elements of an array literal, the sides of `??`.
    ///
    /// As in Hindley–Milner, the branches must have one type — inty
    /// doesn't guess that they form a union (a guess that could depend on
    /// what is known yet about each side). The exceptions, which don't
    /// guess either:
    ///
    /// * literals of one base type widen to it (`1` and `2` join to
    ///   `Number`);
    /// * a value of an (annotated) union or sum joined with one of its
    ///   arms is that union or sum;
    /// * a branch that doesn't complete (`never`) contributes nothing.
    ///
    /// Otherwise it's a `BranchMismatch` error. Where an annotation gives
    /// the expected type, branches are checked against it instead of
    /// joined (`check_expr`, annotated returns), so a union is made by
    /// saying so.
    pub fn join(&mut self, span: Span, t1: &Type, t2: &Type) -> InferResult<Type> {
        // Heads first: the branches may be large (DOM elements), which
        // resolving whole copies.
        let (h1, h2) = (self.zonk_head(t1), self.zonk_head(t2));
        let is_never = |t: &Type| matches!(t, Type::Union(m) if m.is_empty());
        if is_never(&h1) {
            return Ok(h2);
        }
        if is_never(&h2) {
            return Ok(h1);
        }
        // Where widening leaves both alike (it only reaches into a
        // literal, a sum, a tuple or a union of literals, not a record,
        // array or function), the widened attempt below is this one.
        let widens = |t: &Type| {
            matches!(
                t,
                Type::Literal(_) | Type::Maybe(..) | Type::Tuple(_) | Type::Union(_)
            )
        };
        if !widens(&h1) && !widens(&h2) {
            let snap = self.snapshot_inference();
            if self.quietly(|s| s.unify(span, &h1, &h2)).is_ok() {
                return Ok(self.zonk_head(&h1));
            }
            self.restore_snapshot(snap);
        }
        let t1 = self.zonk_arms(t1);
        let t2 = self.zonk_arms(t2);
        if t1 == t2 {
            return Ok(t1);
        }
        // Equal after widening literals (also inside tuples, rows, …) —
        // one attempt: a join's result is widened anyway.
        {
            let (a, b) = (self.widen(span, &t1), self.widen(span, &t2));
            let snap = self.snapshot_inference();
            if self.quietly(|s| s.unify(span, &a, &b)).is_ok() {
                return Ok(self.zonk_head_into(a));
            }
            self.restore_snapshot(snap);
        }
        // A union or sum value joined with one of its arms.
        let is_sum = |t: &Type| matches!(t, Type::Union(_) | Type::Maybe(..));
        if is_sum(&t1) || is_sum(&t2) {
            for (small, big) in [(&t2, &t1), (&t1, &t2)] {
                if !is_sum(big) {
                    continue;
                }
                let snap = self.snapshot_inference();
                if self.quietly(|s| s.subsume(span, small, big)).is_ok() {
                    return Ok(self.zonk_head(big));
                }
                self.restore_snapshot(snap);
            }
        }
        // Rendered (classes by name, variables renamed `a`, `b`, …) if
        // reported: see `render_error`.
        Err(crate::error::TypeError::BranchMismatch {
            left: self.error_type(&t1, &None),
            right: self.error_type(&t2, &None),
            span,
        }
        .into())
    }

    /// The union of two types (normalised), or their unification when
    /// they unify. For *eliminations* of a union that already exists —
    /// reading a property or an index from each arm — where the results
    /// are legitimately "one of these"; not for branches (see
    /// [`Self::join`]).
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
    /// it is safe to call speculatively.
    pub fn union_of(&mut self, span: Span, t1: &Type, t2: &Type) -> Type {
        let t1 = self.zonk_arms(t1);
        let t2 = self.zonk_arms(t2);

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

        if self.quietly(|s| s.unify(span, &t1, &t2)).is_ok() {
            return self.zonk_head(&t1);
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
    /// Subsumption is shallow: it applies to the value flowing, never
    /// inside an array, record, map or set. Those are mutable, so their
    /// contents are invariant and compared by `unify` — a `String[]`
    /// read as a `(String | Number)[]` could be pushed a number through
    /// that alias, and the `String[]` would then hold it (TAPL §15.5:
    /// `Ref T` is invariant). A fresh literal still fits a wider type:
    /// `check_expr` pushes the expected element/field types into it.
    /// Covariance belongs only to an immutable type constructor.
    pub fn subsume(&mut self, span: Span, sub: &Type, sup: &Type) -> InferResult<()> {
        // The rules up to unification look at heads only, and most
        // subsumptions end there: the types are resolved whole only if
        // it fails (unification resolves what it reaches itself).
        let sub_head = super::zonk::zonk_head_cow(&mut self.var_table, sub);
        let sup_head = super::zonk::zonk_head_cow(&mut self.var_table, sup);
        let (sub, sup) = (&*sub_head, &*sup_head);

        // Rule 0 (S-LitBase): `Lit(l) ≤ Base` is sound — every
        // singleton is a value of its base. This rule used to live
        // (symmetrically, hence unsoundly) in `unify`. It's a pure
        // subsumption rule and lives here. The reverse direction
        // `Base ≤ Lit` is intentionally absent.
        if let Type::Literal(lit) = &sub {
            if lit.base_type() == *sup {
                return Ok(());
            }
        }

        // S-Inject, waiting: a variable flowing into a sum may turn out
        // to be the sum, its nothing or a value — which one isn't known
        // yet, so `Inject sub sup` waits for it (binding it to the sum
        // would guess).
        if let (Type::Var(TVarName::Flex(_)), Type::Maybe(..)) = (&sub, &sup) {
            self.add_constraint(TypePred::inject(sub.clone(), sup.clone()), span);
            return Ok(());
        }

        // The same for a sum told apart by `typeof` (`Number | String`):
        // the variable may be the sum or one of its cases.
        if matches!(sub, Type::Var(TVarName::Flex(_))) && matches!(sup, Type::Union(_)) {
            let sup = self.zonk(sup);
            if sup.is_typeof_sum() {
                self.add_constraint(TypePred::inject(sub.clone(), sup), span);
                return Ok(());
            }
        }

        // Rule 1: try unify with rollback so a failed attempt has
        // no observable side-effect on the substitution.
        // Its error is the precise one: in two records, the member that
        // doesn't fit (see `unify_path`). Kept, it is resolved before the
        // restore undoes the bindings it was raised under (speculating,
        // it is dropped anyway).
        let snap = self.snapshot_inference();
        let mut first_err = match self.quietly(|s| s.unify(span, sub, sup)) {
            Ok(()) => return Ok(()),
            Err(e) => e,
        };
        // Reported (not speculating), the error is resolved under the
        // attempt's bindings, and so are the two whole types it is in.
        if self.quiet == 0 && names_member(&first_err) {
            // The attempt was `unify(sub, sup)`: its expected side is
            // `sub`'s, the value supplied; the whole types are `sup`
            // and `sub`.
            if let Some(crate::error::TypeError::UnificationError {
                expected,
                found,
                whole,
                expected_origin,
                found_origin,
                ..
            }) = first_err.as_type_mut()
            {
                std::mem::swap(expected, found);
                std::mem::swap(expected_origin, found_origin);
                *whole = Some(Box::new((
                    crate::error::ShownType::ty(sup),
                    crate::error::ShownType::ty(sub),
                )));
            }
            self.settle_error(&mut first_err);
        }
        self.restore_snapshot(snap);
        let sub = self.zonk_head(sub);
        let sup = self.zonk_head(sup);

        // S-NoThis: a function that uses no `this` (`ArrowThis`) can be
        // called with any, so it flows into a slot for a function with
        // any `this` (a method, or one called detached), but a
        // constructor's (it isn't one). Not the other way: a slot for one
        // that uses none may be called either way.
        if let (Some(sub_this), Some(sup_this)) = (callable_this(&sub), callable_this(&sup)) {
            if matches!(self.zonk_head(&sub_this), Type::ArrowThis)
                && !matches!(self.zonk_head(&sup_this), Type::ArrowThis | Type::NewTarget)
            {
                let sub_as = with_callable_this(&sub, sup_this.clone());
                let snap = self.snapshot_inference();
                if self.quietly(|s| s.unify(span, &sub_as, &sup)).is_ok() {
                    return Ok(());
                }
                self.restore_snapshot(snap);
            }
            // A function that reads `this` where one that uses none is
            // expected: say so, as the types print alike.
            if matches!(self.zonk_head(&sup_this), Type::ArrowThis)
                && !matches!(
                    self.zonk_head(&sub_this),
                    Type::ArrowThis | Type::Var(_) | Type::Error
                )
            {
                let sub_as = with_callable_this(&sub, Type::ArrowThis);
                let snap = self.snapshot_inference();
                let only_this = self.quietly(|s| s.unify(span, &sub_as, &sup)).is_ok();
                self.restore_snapshot(snap);
                if only_this {
                    return Err(crate::error::TypeError::TypeMismatch {
                        expected: format!("{sup}, a function that uses no `this`"),
                        found:
                            "a function that reads `this` (a method says its `this` in its type: \
                                `m: (this: T, …) => R`)"
                                .to_string(),
                        span,
                    }
                    .into());
                }
            }
        }

        // S-FewerParams: a function taking fewer parameters than its slot
        // passes fits it, as a function literal checked against the slot
        // does: JavaScript drops the extra arguments. It fits the slot cut
        // down to its parameters (each still taking what the slot passes
        // there, its result still the slot's). Not the other way: a
        // function needing more arguments than the slot passes would get
        // `undefined` for them.
        if let (Some(n), Some(m)) = (callable_arity(&sub), callable_arity(&sup)) {
            if n < m {
                let cut = with_callable_arity(&sup, n);
                let snap = self.snapshot_inference();
                if self.quietly(|s| s.subsume(span, &sub, &cut)).is_ok() {
                    return Ok(());
                }
                self.restore_snapshot(snap);
            }
        }

        // S-Unroll: an equi-recursive type (a recursive alias) is its
        // unrolling, so subsume against that — one side at a time, so
        // two recursive types never unroll each other forever (those
        // are left to `unify`).
        match (&sub, &sup) {
            (Type::Named(id, args), other) | (other, Type::Named(id, args))
                if !self.is_nominal_type(*id) && !matches!(other, Type::Named(..)) =>
            {
                if let Some(unrolled) = self.unroll_named(*id, args) {
                    return if matches!(sub, Type::Named(..)) {
                        self.subsume(span, &unrolled, &sup)
                    } else {
                        self.subsume(span, &sub, &unrolled)
                    };
                }
            }
            _ => {}
        }

        // S-Inject: a sum takes its nothing, and any value its value
        // takes (a sum of the other nothing too: `T | Undefined` fits
        // `T | Undefined | Null`'s value). The sum itself was taken by
        // unification.
        if let Type::Maybe(z, inner) = &sup {
            if sub == z.ty() {
                return Ok(());
            }
            if let Type::Maybe(z2, sub_inner) = &sub {
                if z2 == z {
                    return self.subsume(span, sub_inner, inner);
                }
            }
            let snap = self.snapshot_inference();
            if self.quietly(|s| s.subsume(span, &sub, inner)).is_ok() {
                return Ok(());
            }
            self.restore_snapshot(snap);
        }

        // Rule 2a (S-UnionL): a union value subsumes into `sup` iff
        // every arm does. Sound by definition — a value of type
        // ⋃τᵢ may be any τᵢ at runtime, so each must fit.
        if let Type::Union(members) = &sub {
            for m in members {
                let m_resolved = self.zonk_head(m);
                self.subsume(span, &m_resolved, &sup)?;
            }
            return Ok(());
        }

        // Rule 2b (S-UnionR): pick a union arm.
        if let Type::Union(members) = &sup {
            let mut matching: Vec<usize> = Vec::new();
            for (i, m) in members.iter().enumerate() {
                let snap = self.snapshot_inference();
                let m_resolved = self.zonk_head(m);
                let ok = self.quietly(|s| s.subsume(span, &sub, &m_resolved)).is_ok();
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
                let chosen = self.zonk_head(&members[matching[0]]);
                return self.subsume(span, &sub, &chosen);
            }
            // A function fits no arm: if one arm is a function type, its
            // mismatch says why (a `this`, a parameter).
            if matching.is_empty() && callable_this(&sub).is_some() {
                let fns: Vec<Type> = members
                    .iter()
                    .map(|m| self.zonk_head(m))
                    .filter(|m| callable_this(m).is_some() || matches!(m, Type::Func { .. }))
                    .collect();
                if let [only] = fns.as_slice() {
                    return self.subsume(span, &sub, only);
                }
            }
            // 0 → no arm fits; >1 → ambiguous. Both fall through to
            // the same error; the diagnostic is best-effort and uses
            // the original sub/sup pair so the user sees the union.
        }

        // Inside two records (an object passed where a class's uses
        // expect one): the member that doesn't fit, and its types, rather
        // than the two whole records (prepared above). Speculating, the
        // error is dropped: the plain one below will do.
        //
        // Otherwise, `expected = sup` (what the slot wants) and `found =
        // sub` (what was supplied).
        let member_err = self.quiet == 0 && names_member(&first_err);
        let mut err = if member_err || self.quiet > 0 {
            first_err
        } else {
            self.unification_error(span, &sup, &sub)
        };
        if self.quiet == 0 {
            let note = match self.row_difference(&sup, &sub) {
                Some(note) => Some(note),
                None => self.invariance_note(span, &sub, &sup),
            };
            if let (Some(note), Some(crate::error::TypeError::UnificationError { context, .. })) =
                (note, err.as_type_mut())
            {
                context.get_or_insert(note);
            }
        }
        Err(err)
    }

    /// When `sub` would fit `sup` if arrays and records were covariant,
    /// the mismatch is only their invariance: say why, and what to do.
    fn invariance_note(&mut self, span: Span, sub: &Type, sup: &Type) -> Option<String> {
        let snap = self.snapshot_inference();
        let fits = self.quietly(|s| s.fits_covariantly(span, sub, sup));
        self.restore_snapshot(snap);
        match (fits, self.main_subst.flatten_bounded(sup, 4_000)) {
            (true, Type::Array(_)) => Some(
                "an array can be written to, so its element type must match exactly \
                 (a push through the expected type could add an element this array \
                 doesn't allow). If it's a function parameter that's only read, make it \
                 generic: `function f<a>(xs: a[]) => …`. Otherwise pass a copy, `[...xs]`, \
                 or declare the array with the wider type"
                    .to_string(),
            ),
            (true, _) => Some(
                "a record's fields can be assigned, so each field's type must match \
                 exactly (an assignment through the expected type could store a value \
                 this record doesn't allow). If it's a function parameter whose fields \
                 are only read, make it generic: `function f<a>(r: {x: a}) => …`. \
                 Otherwise declare the record with the wider type"
                    .to_string(),
            ),
            _ => None,
        }
    }

    /// Would `sub ≤ sup` hold if array elements and record fields were
    /// covariant? Only for a diagnostic — it is unsound as a rule.
    fn fits_covariantly(&mut self, span: Span, sub: &Type, sup: &Type) -> bool {
        let inner = |s: &mut Self, a: &Type, b: &Type| {
            s.subsume(span, a, b).is_ok() || s.fits_covariantly(span, a, b)
        };
        match (
            self.main_subst.flatten_bounded(sub, 4_000),
            self.main_subst.flatten_bounded(sup, 4_000),
        ) {
            (Type::Array(a), Type::Array(b)) | (Type::Map(a), Type::Map(b)) => inner(self, &a, &b),
            (Type::Row(r1), Type::Row(r2))
                if r1.is_closed() && r2.is_closed() && r1.props.keys().eq(r2.props.keys()) =>
            {
                r1.props
                    .iter()
                    .zip(r2.props.values())
                    .all(|((_, f1), f2)| inner(self, &f1.ty, &f2.ty))
            }
            _ => false,
        }
    }

    /// For two record types, which fields one has and the other lacks:
    /// what a mismatch between them is usually about.
    fn row_difference(&self, expected: &Type, found: &Type) -> Option<String> {
        let (Type::Row(e), Type::Row(f)) = (
            self.main_subst.flatten_bounded(expected, 4_000),
            self.main_subst.flatten_bounded(found, 4_000),
        ) else {
            return None;
        };
        let visible = |r: &crate::types::RowType| -> Vec<String> {
            r.props
                .iter()
                .filter(|(k, v)| {
                    k.0 != crate::types::CALLABLE_KEY
                        && matches!(
                            self.main_subst.resolve_presence(&v.presence),
                            crate::types::Presence::Pre
                        )
                })
                .map(|(k, _)| k.0.clone())
                .collect()
        };
        let (ek, fk) = (visible(&e), visible(&f));
        let missing: Vec<&String> = ek
            .iter()
            .filter(|k| !f.props.contains_key(&crate::types::PropName((*k).clone())))
            .collect();
        let extra: Vec<&String> = if e.is_closed() {
            fk.iter()
                .filter(|k| !e.props.contains_key(&crate::types::PropName((*k).clone())))
                .collect()
        } else {
            Vec::new()
        };
        let list = |ks: &[&String]| {
            let mut shown: Vec<String> = ks.iter().take(5).map(|k| format!("'{k}'")).collect();
            if ks.len() > 5 {
                shown.push(format!("… and {} more", ks.len() - 5));
            }
            shown.join(", ")
        };
        match (missing.is_empty(), extra.is_empty()) {
            (true, true) => None,
            (false, true) => Some(format!(
                "missing field{} {}",
                plural(missing.len()),
                list(&missing)
            )),
            (true, false) => Some(format!(
                "unexpected field{} {} (the expected record type is closed)",
                plural(extra.len()),
                list(&extra)
            )),
            (false, false) => Some(format!(
                "missing field{} {}; unexpected field{} {}",
                plural(missing.len()),
                list(&missing),
                plural(extra.len()),
                list(&extra)
            )),
        }
    }

    /// "Either-direction" subsumption used by symmetric operators
    /// like `===`, `!==`, and ordering comparisons, where the two
    /// operands just need to have a common possible value — neither
    /// flow-direction is privileged. Try `subsume(t1, t2)` then
    /// `subsume(t2, t1)`; commit on the first one that succeeds, fail
    /// with the original error if neither does.
    pub fn subsume_either(&mut self, span: Span, t1: &Type, t2: &Type) -> InferResult<()> {
        let snap = self.snapshot_inference();
        if self.quietly(|s| s.subsume(span, t1, t2)).is_ok() {
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
        span: crate::span::Span,
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
        let ty = std::sync::Arc::new(ty);
        self.mirror_extend(&var, &ty);
        self.main_subst.insert_shared(var.clone(), ty.clone());
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
        // Both sides write the binding out as a tree: one that mentions
        // large types in many places (elements chained through
        // `appendChild`) is exponentially larger, and the check alone
        // would run out of memory. Such a binding isn't probed.
        const PROBE_CAP: usize = 20_000;
        if self.main_subst.flattened_size(&ty_var, PROBE_CAP) >= PROBE_CAP {
            return;
        }
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
    fn mirror_extend(&mut self, var: &TVarName, ty: &std::sync::Arc<Type>) {
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
        if let Type::Var(TVarName::Flex(other)) = &**ty {
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
        if self.var_table.is_free(root) {
            self.var_table.bind_shared(root, ty.clone());
        } else {
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
    }

    /// Bind a presence variable to a presence. Same collision-as-unify
    /// discipline as `extend_subst` for type variables.
    pub fn extend_subst_presence(
        &mut self,
        span: crate::span::Span,
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
        span: crate::span::Span,
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
        self.closed_named.remove(&def.id);
        self.named_types.insert(def.id, def);
    }

    /// Look up a named type definition.
    pub fn get_named_type(&self, id: TypeId) -> Option<&TypeDef> {
        self.named_types.get(&id)
    }

    /// Map from `TypeId` to declared name for every *named* type
    /// definition (brands and any other named def). Feeds
    /// `PrettyContext::with_nominal_names` so diagnostics and the
    /// printed program type render a brand as `UserId` / `Box<Number>`
    /// rather than the internal `μ<id>`. Anonymous equi-recursive types
    /// carry no name and are absent from the map.
    pub fn nominal_names(&self) -> HashMap<TypeId, String> {
        self.named_types
            .iter()
            .filter_map(|(id, def)| def.name.clone().map(|n| (*id, n)))
            .collect()
    }

    /// The printer for the types a user is shown (diagnostics, and the
    /// language server's hover and hints): brands and recursive aliases
    /// by their names, and a type that is another alias's body, its
    /// parameters instantiated, by that alias's name (`PaletteItem`,
    /// `DomEvent<a>`, rather than their records). An alias is structural,
    /// so a type equal to its body is that alias, wherever it came from.
    pub fn printer(&self) -> crate::types::PrettyContext {
        let mut aliases: Vec<(String, Vec<u32>, Type)> = self
            .type_aliases
            .iter()
            .filter(|(_, d)| d.nominal_id.is_none() && d.rec_id.is_none() && !d.open_arity)
            .filter(|(_, d)| matches!(d.body, Type::Row(_) | Type::Union(_) | Type::Maybe(..)))
            .map(|(n, d)| (n.clone(), d.params.clone(), d.body.clone()))
            .collect();
        // Deterministic: of aliases with equal bodies, the first by name
        // (`DomEvent` first, over its synonyms `PointerEvent`, …).
        aliases.sort_by(|a, b| {
            let rank = |n: &str| if n == "DomEvent" { 0 } else { 1 };
            (rank(&a.0), &a.0).cmp(&(rank(&b.0), &b.0))
        });
        crate::types::PrettyContext::with_nominal_names(self.nominal_names())
            .naming_aliases(aliases)
    }

    /// Whether `id` refers to a declared nominal (branded) type rather
    /// than an auto-generated equi-recursive type. Drives unification:
    /// nominal types never unroll for identity.
    pub fn is_nominal_type(&self, id: TypeId) -> bool {
        self.named_types.get(&id).is_some_and(|d| d.nominal)
    }

    /// The key an identifier `name` at `span` (a use, a declaration or an
    /// assignment target) is bound under: the declaration binding
    /// resolution found, or the name for a global.
    pub(in crate::infer) fn key_of(&self, span: Span, name: &str) -> crate::infer::env::Key {
        match self.resolution.local_at(span, name) {
            Some(id) => crate::infer::env::Key::Local(id),
            None => crate::infer::env::Key::Name(name.to_string()),
        }
    }

    /// Declare the identifier `name` at `span` with `scheme`.
    pub(in crate::infer) fn bind(
        &mut self,
        env: &crate::infer::TypeEnv,
        span: Span,
        name: &str,
        scheme: TypeScheme,
        mutability: crate::infer::env::Mutability,
    ) -> Result<crate::infer::TypeEnv, crate::error::IntyError> {
        let key = self.key_of(span, name);
        self.rebind(env, key, span, name, scheme, mutability)
    }

    /// Bind `key` (the identifier `name` declared at `span`) to `scheme`,
    /// replacing any binding it had here: a hoisted placeholder takes its
    /// final scheme. A binding read before its declaration (hoisting)
    /// takes this type, and a second declaration of the same binding
    /// elsewhere must agree with the first.
    pub(in crate::infer) fn rebind(
        &mut self,
        env: &crate::infer::TypeEnv,
        key: crate::infer::env::Key,
        span: Span,
        name: &str,
        scheme: TypeScheme,
        mutability: crate::infer::env::Mutability,
    ) -> Result<crate::infer::TypeEnv, crate::error::IntyError> {
        if let crate::infer::env::Key::Local(id) = &key {
            if let Some((forward, _, _)) = self.forward_locals.remove(id) {
                let ty = self.instantiate(&scheme);
                self.unify(span, &forward, &ty)?;
            }
            match self.local_decl_spans.get(id) {
                Some(first) if *first != span => {
                    if let Some(earlier) = self.local_types.get(id).cloned() {
                        let earlier = self.instantiate(&earlier);
                        let now = self.instantiate(&scheme);
                        self.unify(span, &earlier, &now)?;
                    }
                }
                Some(_) => {}
                None => {
                    self.local_decl_spans.insert(*id, span);
                }
            }
            self.local_types.insert(*id, scheme.clone());
        }
        Ok(env.extend_key(
            key,
            name,
            crate::infer::env::Binding {
                scheme,
                mutability,
                declared: None,
            },
        ))
    }

    /// The binding the identifier `name` at `span` refers to. A binding
    /// of the program that `env` doesn't hold comes from `local_types`
    /// (and is held fixed in generalisation from then on); one not
    /// declared yet gets a fresh type its declaration will unify with.
    /// `None` only for an unknown global.
    pub(in crate::infer) fn read_binding(
        &mut self,
        env: &crate::infer::TypeEnv,
        span: Span,
        name: &str,
    ) -> Option<crate::infer::env::Binding> {
        let key = self.key_of(span, name);
        if let Some(b) = env.lookup_key(&key) {
            return Some(b.clone());
        }
        let crate::infer::env::Key::Local(id) = key else {
            return None;
        };
        self.escaped_locals.insert(id);
        let scheme = match self.local_types.get(&id) {
            Some(s) => s.clone(),
            None => {
                let var = self.fresh_type_var();
                self.forward_locals
                    .insert(id, (var.clone(), name.to_string(), span));
                let s = TypeScheme::mono(var);
                self.local_types.insert(id, s.clone());
                s
            }
        };
        Some(crate::infer::env::Binding::mutable(scheme))
    }

    /// Unroll a named recursive type by substituting its definition.
    pub fn unroll_named(&self, id: TypeId, args: &[Type]) -> Option<Type> {
        let def = self.named_types.get(&id)?;

        // Parameters to arguments, at once: an argument may mention a
        // parameter (the body unrolled at its own parameter), which a
        // transitive substitution would replace again, without end.
        let mut subst = Subst::simultaneous();
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
        self.type_classes.insert(class.name, class);
    }

    /// Instantiate a type scheme with fresh flexible variables (both
    /// type and presence). Each use site sees independent presence
    /// variables, so a scheme like `<θ>{x:Number, y:θ(String)} -> R`
    /// can be called once supplying `y` and once omitting it.
    pub fn instantiate(&mut self, scheme: &TypeScheme) -> Type {
        self.instantiate_recording(scheme).0
    }

    /// [`Self::instantiate`], also returning which fresh type replaced
    /// each quantified variable (empty for a monomorphic scheme).
    pub fn instantiate_recording(&mut self, scheme: &TypeScheme) -> (Type, Vec<(TVarName, Type)>) {
        self.instantiate_recording_at(scheme, Span::new(0, 0))
    }

    /// [`Self::instantiate_recording`] for a use at `span`, where the
    /// scheme's predicates are then checked (and reported).
    pub fn instantiate_recording_at(
        &mut self,
        scheme: &TypeScheme,
        span: Span,
    ) -> (Type, Vec<(TVarName, Type)>) {
        if scheme.is_mono() {
            return (scheme.body.ty.clone(), Vec::new());
        }

        let mut subst = Subst::empty();
        let mut instantiation = Vec::with_capacity(scheme.vars.len());
        for var in &scheme.vars {
            let fresh = self.fresh_type_var();
            instantiation.push((var.clone(), fresh.clone()));
            subst.insert(var.clone(), fresh);
        }
        for pvar in &scheme.pvars {
            let fresh = self.fresh_pvar();
            subst.insert_presence(pvar.clone(), crate::types::Presence::Var(fresh));
        }

        // Also instantiate predicates as pending constraints
        for pred in &scheme.body.preds {
            let instantiated_pred = subst.apply(pred);
            self.pending_constraints.push(PendingConstraint {
                pred: instantiated_pred,
                span,
            });
        }

        (subst.apply(&scheme.body.ty), instantiation)
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
            subst.insert_presence(pvar.clone(), crate::types::Presence::Var(skolem));
        }

        (skolems, subst.apply(&scheme.body.ty))
    }

    /// Settle the `this` of callees called detached that weren't known
    /// at the call (`pending_detached`): one that uses no `this`, or is
    /// `Undefined`, was right to be; a method (which reads its object)
    /// is an error; one still unknown is pinned to `Undefined` unless the
    /// environment fixes it (`fixed`, at a generalisation: it would be
    /// generalised, in the type or in a constraint), and always when
    /// `fixed` is `None` (the program is done). Whether anything was
    /// pinned.
    pub(crate) fn settle_detached(
        &mut self,
        fixed: Option<&std::collections::HashSet<TVarName>>,
    ) -> bool {
        let mut pinned = false;
        let mut keep = Vec::new();
        let methods: std::collections::HashSet<crate::types::TVarId> = self
            .method_this_vars
            .clone()
            .into_iter()
            .filter_map(|id| self.var_table.find_if_present(id))
            .collect();
        for (this, span, callee) in std::mem::take(&mut self.pending_detached) {
            match self.zonk_head(&this) {
                Type::ArrowThis | Type::Undefined | Type::Error | Type::NewTarget => {}
                Type::Var(v) => {
                    if fixed.is_none_or(|fixed| !fixed.contains(&v)) {
                        // A function whose body mentions `this` reads it, as
                        // `undefined` here; any other uses none (a function
                        // type whose body isn't seen says so), which a
                        // detached call accepts and an arrow function has.
                        let reads = matches!(&v, TVarName::Flex(id)
                            if self.var_table.find_if_present(*id).is_some_and(|r| methods.contains(&r)));
                        let pin = if reads {
                            Type::Undefined
                        } else {
                            Type::ArrowThis
                        };
                        if let Err(e) = self.unify(span, &Type::Var(v), &pin) {
                            self.push_error(e);
                        }
                        pinned = true;
                    } else {
                        keep.push((this, span, callee));
                    }
                }
                _ => self.push_error(crate::error::TypeError::DetachedThis { callee, span }.into()),
            }
        }
        self.pending_detached.extend(keep);
        pinned
    }

    /// Settle the `this` of callees called as methods that weren't known
    /// at the call (`pending_receivers`). One now known is checked against
    /// the receiver as at the call (`unify_this`): no `this`, or the
    /// receiver. One that is the `this` of a function whose body mentions
    /// `this` (`method_this_vars`) is that function's: it is called on the
    /// receiver. One still unknown stays unknown until the type being
    /// generalised reaches it (`reached`), and is then (and always when
    /// `reached` is `None`, the program done) a function that uses no
    /// `this`: a function type whose body isn't seen says it uses none,
    /// as an annotation does, and a call never makes a function a
    /// method. Whether anything was decided.
    pub(crate) fn settle_receivers(
        &mut self,
        reached: Option<&std::collections::HashSet<TVarName>>,
    ) -> bool {
        let mut decided = false;
        let mut keep = Vec::new();
        let methods: std::collections::HashSet<crate::types::TVarId> = self
            .method_this_vars
            .clone()
            .into_iter()
            .filter_map(|id| self.var_table.find_if_present(id))
            .collect();
        for pending in std::mem::take(&mut self.pending_receivers) {
            let PendingReceiver {
                this,
                receiver,
                span,
                unknown_is_method,
            } = pending.clone();
            let result = match self.zonk_head(&this) {
                Type::Var(TVarName::Flex(id))
                    if self
                        .var_table
                        .find_if_present(id)
                        .is_some_and(|r| methods.contains(&r)) =>
                {
                    self.record_origin(
                        TVarName::Flex(id),
                        TypeOrigin::MethodCall {
                            method: String::new(),
                            span,
                        },
                    );
                    self.unify_this(span, &this, &receiver)
                }
                Type::Var(v) if v.is_flex() => {
                    // (A call on a value an importer decides waits for the
                    // importers: at the end of an imported module, the one
                    // that decides it may still be to come.)
                    if reached.is_some_and(|r| !r.contains(&v))
                        || (unknown_is_method && reached.is_none() && self.module_depth > 0)
                    {
                        keep.push(pending);
                        continue;
                    }
                    if unknown_is_method {
                        self.unify_this(span, &this, &receiver)
                    } else {
                        self.unify(span, &Type::Var(v), &Type::ArrowThis)
                    }
                }
                _ => self.unify_this(span, &this, &receiver),
            };
            decided = true;
            if let Err(e) = result {
                self.push_error(e);
            }
        }
        self.pending_receivers.extend(keep);
        decided
    }

    /// Settle the `return`s of `async` bodies whose value's type wasn't
    /// known (`pending_async_returns`): a promise gives its value, any
    /// other type itself. One still unknown stays while the environment
    /// fixes it (`fixed`), and otherwise (always when `fixed` is `None`)
    /// is taken to be a value, as before `return`s of promises were
    /// told apart. Whether anything was decided.
    pub(crate) fn settle_async_returns(
        &mut self,
        fixed: Option<&std::collections::HashSet<TVarName>>,
    ) -> bool {
        let mut decided = false;
        let mut keep = Vec::new();
        for (ty, value, span) in std::mem::take(&mut self.pending_async_returns) {
            let result = match self.zonk_head(&ty) {
                Type::Promise(inner) => self.unify(span, &value, &inner),
                Type::Var(v) if v.is_flex() && fixed.is_some_and(|f| f.contains(&v)) => {
                    keep.push((ty, value, span));
                    continue;
                }
                _ => self.unify(span, &value, &ty),
            };
            decided = true;
            if let Err(e) = result {
                self.push_error(e);
            }
        }
        self.pending_async_returns.extend(keep);
        decided
    }

    /// Check the parameters (and fields) calls filled or skipped without
    /// deciding them (`pending_optional_params`). One decided since must
    /// agree with the call: a call can't skip one the function requires,
    /// nor pass one it doesn't take. One still undecided stays pending
    /// (and, at a generalisation, isn't quantified: see
    /// `generalize_seeded`), so a later decision is still checked; at the
    /// end (`done`) it is dropped: the call was fine either way. Returns
    /// the presence variables still pending.
    pub(crate) fn settle_optional_params(
        &mut self,
        done: bool,
    ) -> std::collections::HashSet<crate::types::PVarName> {
        use crate::types::Presence;
        let mut keep = Vec::new();
        let mut open = std::collections::HashSet::new();
        for (v, passed, span) in std::mem::take(&mut self.pending_optional_params) {
            let wanted = if passed { Presence::Pre } else { Presence::Abs };
            match self.main_subst.resolve_presence(&Presence::Var(v.clone())) {
                Presence::Var(now) => {
                    if !done {
                        open.insert(now.clone());
                        keep.push((now, passed, span));
                    }
                }
                decided if decided == wanted => {}
                _ => self.push_error(
                    crate::error::TypeError::TypeMismatch {
                        expected: if passed {
                            "a function that takes this argument".to_string()
                        } else {
                            "a function that may be called without this argument".to_string()
                        },
                        found: if passed {
                            "one that takes fewer".to_string()
                        } else {
                            "one that requires it".to_string()
                        },
                        span,
                    }
                    .into(),
                ),
            }
        }
        self.pending_optional_params.extend(keep);
        open
    }

    /// Generalize a type over free variables not in the environment.
    /// Also collects relevant predicates from pending_constraints.
    /// Generalizes over presence variables too (Remy '94), with the
    /// same env-difference rule.
    pub fn generalize(&mut self, env_free: &crate::infer::EnvFree, ty: &Type) -> TypeScheme {
        self.generalize_seeded(env_free, ty, &[])
    }

    /// [`Self::generalize`], quantifying the variables `extra` too (where
    /// the environment doesn't fix them), with the constraints on them: a
    /// mutually recursive group's members are generalised over the same
    /// variables (see `infer_function_group`).
    pub fn generalize_seeded(
        &mut self,
        env_free: &crate::infer::EnvFree,
        ty: &Type,
        extra: &[TVarName],
    ) -> TypeScheme {
        self.constraint_removals += 1;
        // A type too large to write out isn't generalised: it keeps its
        // monomorphic type (sound, if less general) rather than be copied
        // into a scheme.
        if self.too_large_to_generalise(ty) {
            return TypeScheme::mono(ty.clone());
        }
        // Flatten row tails through the substitution before
        // computing free vars. `apply_subst` is shallow on tails
        // for performance reasons; without flattening here, a
        // function whose parameter row picked up extra fields via
        // later property-access constraints would generalise to a
        // scheme that's missing those fields, letting calls with
        // incompatible argument shapes through. See
        // `Subst::flatten` for the full story.
        // A `Plus` on a known type is decided, not carried in the scheme.
        if let Err(e) = self.resolve_known_plus() {
            self.push_error(e);
        }
        let mut ty = self.main_subst.flatten(ty);
        let (fixed_vars, fixed_pvars) = self.env_fixed_vars(env_free, &ty);
        // A method call's `this` first: a callee called both on a receiver
        // and detached that doesn't read `this` uses none, which both
        // calls accept; settling the detached call first would pin it to
        // `Undefined`, which the method call's receiver then contradicts.
        if !self.pending_receivers.is_empty() {
            // The variables generalising would quantify: the type's, and
            // those of the constraints it may carry.
            let mut reached = ty.free_vars();
            for c in &self.pending_constraints {
                let mut r = crate::types::subst::Reach::default();
                for t in &c.pred.types {
                    self.main_subst.reach(t, &mut r);
                }
                reached.extend(r.vars);
            }
            reached.retain(|v| !fixed_vars.contains(v));
            if self.settle_receivers(Some(&reached)) {
                ty = self.main_subst.flatten(&ty);
            }
        }
        // A detached call's `this` that would be generalised is settled
        // then: as `Undefined`, what the call passes. (Which variables
        // the environment fixes doesn't change: one is bound to a type
        // without variables.)
        if !self.pending_detached.is_empty() && self.settle_detached(Some(&fixed_vars)) {
            ty = self.main_subst.flatten(&ty);
        }
        if !self.pending_async_returns.is_empty() && self.settle_async_returns(Some(&fixed_vars)) {
            ty = self.main_subst.flatten(&ty);
        }
        // What a `return` still waiting gives its promise is decided when
        // the returned type is: it isn't generalised meanwhile (an
        // instance would keep a variable the settling never reaches).
        let mut fixed_vars = fixed_vars;
        for (_, value, _) in &self.pending_async_returns {
            fixed_vars.extend(self.main_subst.flatten(value).free_vars());
        }
        // A parameter or field a call filled or skipped without deciding
        // isn't generalised while it is undecided: a generalised
        // function's callers would decide it apart from the call (one
        // passing a callback that needs the argument the call left out).
        // Kept monomorphic, a later decision is still checked against the
        // call (`settle_optional_params`).
        let mut fixed_pvars = fixed_pvars;
        if !self.pending_optional_params.is_empty() {
            fixed_pvars.extend(self.settle_optional_params(false));
        }
        let mut ty_vars = ty.free_vars();
        ty_vars.extend(extra.iter().cloned());
        let pvars = ty.free_pvars();

        // Sort by TVarName id so the scheme's quantification order is
        // deterministic. `ty.free_vars()` returns a HashSet, whose
        // iteration order isn't stable even within a process — each
        // HashSet is seeded independently — which would otherwise make
        // the printed scheme `<a, b>...` non-deterministically map
        // letters to type-var slots across runs.
        // A variable that is bound in the substitution is not free, whatever
        // a (shallow) traversal of `ty` reports; `flatten` expands each
        // variable once, so a bound variable can survive in its output.
        let mut gen_vars: Vec<TVarName> = ty_vars
            .into_iter()
            .filter(|v| v.is_flex() && !fixed_vars.contains(v))
            .filter(|v| {
                let var = Type::Var(v.clone());
                self.zonk_head(&var) == var
            })
            .collect();
        gen_vars.sort_by_key(|v| v.id());

        // Presence variables follow the same rule as type variables: a
        // pvar reachable from the environment (e.g. an optional field of
        // a row a parameter's type is bound to) must stay monomorphic.
        let mut gen_pvars: Vec<crate::types::PVarName> = pvars
            .into_iter()
            .filter(|p| p.is_flex() && !fixed_pvars.contains(p))
            .collect();
        gen_pvars.sort_by_key(|p| p.id());

        if gen_vars.is_empty() && gen_pvars.is_empty() {
            #[cfg(debug_assertions)]
            self.debug_check_generalisation(env_free, &gen_vars);
            TypeScheme::mono(ty)
        } else {
            // Collect the predicates that involve the generalized
            // variables. Their other variables are quantified too unless
            // the environment fixes them: a predicate's variable that the
            // type doesn't mention (the result of an unused `s.length`, or
            // of an `xs[i]`) must not be shared by every instantiation.
            // Quantifying one can pull in further predicates, so iterate.
            let mut gen_var_set: std::collections::HashSet<_> = gen_vars.iter().cloned().collect();
            let mut gen_pvar_set: std::collections::HashSet<_> =
                gen_pvars.iter().cloned().collect();
            let mut scheme_preds = Vec::new();
            let mut remaining: Vec<PendingConstraint> =
                std::mem::take(&mut self.pending_constraints);
            // Each constraint's variables through the substitution
            // (`reach`: a flattened copy can be far larger).
            let reach_of = |s: &Self, c: &PendingConstraint| {
                let mut r = crate::types::subst::Reach::default();
                for t in &c.pred.types {
                    s.main_subst.reach(t, &mut r);
                }
                r
            };
            loop {
                let mut rest = Vec::new();
                let mut took = false;
                for constraint in remaining {
                    // Whether it mentions a generalised variable, found
                    // without building its flattened types.
                    let reach = reach_of(self, &constraint);
                    if reach.vars.iter().any(|v| gen_var_set.contains(v)) {
                        let mut pred = self.apply_subst_pred(&constraint.pred);
                        // Flattened, as the type is: a row's bound tail (a
                        // `Spread`'s rows) would otherwise be left out of the
                        // quantified variables and shared by every instance.
                        for t in pred.types.iter_mut() {
                            *t = self.main_subst.flatten(t);
                        }
                        // Where the requirement is written, for a failure of
                        // one of its instances at a call.
                        pred.origin.get_or_insert(constraint.span);
                        for v in reach.vars {
                            if v.is_flex()
                                && !fixed_vars.contains(&v)
                                && self.zonk_head(&Type::Var(v.clone())) == Type::Var(v.clone())
                                && gen_var_set.insert(v.clone())
                            {
                                gen_vars.push(v);
                            }
                        }
                        for p in reach.pvars {
                            if p.is_flex()
                                && !fixed_pvars.contains(&p)
                                && gen_pvar_set.insert(p.clone())
                            {
                                gen_pvars.push(p);
                            }
                        }
                        scheme_preds.push(pred);
                        took = true;
                    } else {
                        rest.push(constraint);
                    }
                }
                remaining = rest;
                if !took {
                    break;
                }
            }
            self.pending_constraints = remaining;
            // A write constraint, or a `Testable`, whose type is already
            // known is decided here, not carried in the scheme to be found
            // out at each use (lean/ROADMAP.md, phase 1). On a variable it
            // stays. (A
            // `Plus` on a known type was decided by `simplify_has_props`.)
            let scheme_preds: Vec<TypePred> = scheme_preds
                .into_iter()
                .filter(|pred| {
                    if !matches!(
                        pred.class,
                        ClassName::IndexWrite | ClassName::FieldWrite | ClassName::Testable
                    ) {
                        return true;
                    }
                    let ty = self.main_subst.flatten(&pred.types[0]);
                    if matches!(ty, Type::Var(_)) {
                        return true;
                    }
                    let span = pred.origin.unwrap_or_default();
                    let decided = match pred.as_field_write() {
                        Some((_, name)) => {
                            let name = name.to_string();
                            self.resolve_field_write(&ty, &name, span)
                        }
                        None if pred.class == ClassName::Testable => {
                            self.resolve_testable(&ty, span)
                        }
                        None => self.resolve_index_write(&ty, span),
                    };
                    if let Err(e) = decided {
                        self.push_error(e);
                    }
                    false
                })
                .collect();
            // Of what the scheme took, a constraint whose subject (see
            // `ClassName::subject_positions`) nothing in the scheme reaches — not
            // its type, nor a constraint the type reaches — is vacuous in
            // every instance: there its subject is a fresh variable that
            // can be whatever meets it, and no caller sees it. Left in, it
            // shows as a requirement on a variable nothing mentions (an
            // instance of a generalised `const` relating to a placeholder
            // nothing used, an `Iterable` posed for an argument a call
            // left out). Only the scheme loses it: what stays pending is
            // what it would be with it, so a variable still to be decided
            // elsewhere (an enclosing function's `return`s) is still
            // checked when it is.
            let mut reached: std::collections::HashSet<TVarName> = ty.free_vars();
            reached.extend(extra.iter().cloned());
            reached.extend(fixed_vars.iter().cloned());
            let mut kept = vec![false; scheme_preds.len()];
            loop {
                let mut changed = false;
                for (i, pred) in scheme_preds.iter().enumerate() {
                    let subject_reached = pred
                        .class
                        .subject_positions(pred.types.len())
                        .iter()
                        .any(|&k| match &pred.types[k] {
                            Type::Var(v) if v.is_flex() => reached.contains(v),
                            // A known subject decides the constraint (or
                            // fails it at an instance): it isn't vacuous.
                            _ => true,
                        });
                    if !kept[i] && subject_reached {
                        kept[i] = true;
                        changed = true;
                        for t in &pred.types {
                            reached.extend(t.free_vars());
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            let scheme_preds: Vec<TypePred> = scheme_preds
                .into_iter()
                .zip(kept)
                .filter_map(|(pred, kept)| kept.then_some(pred))
                .collect();
            // A variable only a dropped constraint mentioned is nobody's.
            gen_vars.retain(|v| reached.contains(v));
            gen_vars.sort_by_key(|v| v.id());
            gen_pvars.sort_by_key(|p| p.id());

            #[cfg(debug_assertions)]
            self.debug_check_generalisation(env_free, &gen_vars);

            let mut tidy: Vec<TypePred> = Vec::new();
            for p in scheme_preds {
                if !tidy.contains(&p) {
                    tidy.push(p);
                }
            }
            let scheme_preds = tidy;
            TypeScheme::qualified_with_presence(gen_vars, gen_pvars, scheme_preds, ty)
        }
    }

    /// The type variables `env`'s bindings reach (through the
    /// substitution and named types): what a module leaves for its
    /// importers to decide.
    pub fn reachable_vars(
        &mut self,
        env: &crate::infer::TypeEnv,
    ) -> std::collections::HashSet<TVarName> {
        self.env_fixed_vars(&env.free(), &Type::Undefined).0
    }

    /// The type and presence variables generalisation must leave alone.
    ///
    /// This is the textbook `ftv(S Γ)` — the environment's free variables
    /// *after* applying the current substitution — plus two extensions:
    ///
    /// * **Named-type bodies.** Free-variable functions stop at
    ///   `Named(id, …)`, but a recursive or nominal type's body can mention
    ///   variables other than its parameters, and instantiating a scheme
    ///   can't copy those (the body is shared). Every such variable reachable
    ///   from the environment *or from `ty`* is kept monomorphic.
    /// * **Functional dependencies of pending constraints.** A variable
    ///   determined by fixed variables is fixed too. For
    ///   `Indexable(container, index, element)` the container determines the
    ///   other two — `NAMES[i]` with `NAMES` still an environment
    ///   placeholder fixes the element — but a fixed *index* alone fixes
    ///   nothing (`o[KEY]` stays polymorphic in `o`). `Plus` has a single
    ///   argument, so it never propagates. A predicate that mixes fixed and
    ///   generalised variables goes into the scheme as usual (HM(X)).
    ///
    /// Callers pass `env.free()` of the unsubstituted environment. A
    /// variable in it may since have been bound to a type mentioning other
    /// variables — e.g. the placeholder `infer_stmt_list` pre-binds for a
    /// top-level `const` that a hoisted function uses before the `const`
    /// is inferred. Quantifying those would let the function's scheme
    /// disagree with the `const`'s eventual type (and, once the `const` is
    /// inferred, corrupt it).
    pub(in crate::infer) fn env_fixed_vars(
        &mut self,
        env_free: &crate::infer::EnvFree,
        ty: &Type,
    ) -> (
        std::collections::HashSet<TVarName>,
        std::collections::HashSet<crate::types::PVarName>,
    ) {
        use std::collections::HashSet;
        let mut vars: HashSet<TVarName> = HashSet::new();
        let mut pvars: HashSet<crate::types::PVarName> = env_free.pvars.clone();
        let mut named: Vec<TypeId> = env_free.named.iter().copied().collect();
        // Bindings reached outside the environment count as in it.
        let mut env_vars: Vec<TVarName> = env_free.vars.iter().cloned().collect();
        for id in &self.escaped_locals {
            if let Some(scheme) = self.local_types.get(id) {
                env_vars.extend(scheme.free_vars());
                pvars.extend(scheme.free_pvars());
                named.extend(scheme.body.ty.named_ids());
            }
        }
        // What the environment's variables reach through the
        // substitution (without building their flattened types, which can
        // be far larger than the substitution: see `Subst::reach`).
        let mut reach = crate::types::subst::Reach::default();
        for v in &env_vars {
            vars.insert(v.clone());
            self.main_subst.reach(&Type::Var(v.clone()), &mut reach);
        }
        // Presence variables bound in the substitution resolve too.
        let bound_pvars: Vec<crate::types::PVarName> = pvars.iter().cloned().collect();
        for p in bound_pvars {
            if let Some(crate::types::Presence::Var(q)) = self.main_subst.get_presence(&p).cloned()
            {
                pvars.insert(q);
            }
        }
        // Variables inside named-type bodies reachable from the environment,
        // from `ty` itself, or from a pending constraint (which
        // `generalize` may take into the scheme and quantify the
        // variables of: one that also sits in a shared body would then
        // come apart from it in each instance).
        named.extend(ty.named_ids());
        for c in &self.pending_constraints {
            for t in &c.pred.types {
                let mut r = crate::types::subst::Reach::default();
                self.main_subst.reach(t, &mut r);
                named.extend(r.named);
            }
        }
        vars.extend(reach.vars);
        pvars.extend(reach.pvars);
        named.extend(reach.named);
        let mut seen: HashSet<TypeId> = HashSet::new();
        while let Some(id) = named.pop() {
            if !seen.insert(id) || self.closed_named.contains(&id) {
                continue;
            }
            let Some(def) = self.named_types.get(&id) else {
                continue;
            };
            let params: HashSet<TVarName> = def.params.iter().cloned().collect();
            // What the body reaches through the substitution, found
            // without writing it out (a body holding element types is
            // exponentially larger as a tree: see `Subst::reach`).
            let mut body = crate::types::subst::Reach::default();
            let def_body = def.body.clone();
            self.main_subst.reach(&def_body, &mut body);
            let free: Vec<TVarName> = body
                .vars
                .into_iter()
                .filter(|v| !params.contains(v))
                .collect();
            let free_pvars = body.pvars;
            let inner: Vec<TypeId> = body.named.into_iter().filter(|n| *n != id).collect();
            // Only its parameters, and named types that are closed too: no
            // substitution reaches inside it again.
            if free.is_empty()
                && free_pvars.is_empty()
                && inner.iter().all(|n| self.closed_named.contains(n))
            {
                self.closed_named.insert(id);
            }
            vars.extend(free);
            pvars.extend(free_pvars);
            named.extend(inner);
        }
        // Close over the pending constraints' functional dependencies:
        // each type's free variables through the substitution (`reach`,
        // not a flattened copy of it).
        let preds: Vec<(ClassName, Vec<crate::types::subst::Reach>)> = self
            .pending_constraints
            .iter()
            .map(|c| {
                let reaches = c
                    .pred
                    .types
                    .iter()
                    .map(|t| {
                        let mut r = crate::types::subst::Reach::default();
                        self.main_subst.reach(t, &mut r);
                        r
                    })
                    .collect();
                (c.pred.class, reaches)
            })
            .collect();
        loop {
            let mut changed = false;
            for (class, types) in &preds {
                let fixed = |r: &crate::types::subst::Reach| r.vars.is_subset(&vars);
                let determined: Vec<&crate::types::subst::Reach> = match (class, types.as_slice()) {
                    // container → index, element
                    (ClassName::Indexable, [container, index, element]) => {
                        if fixed(container) {
                            vec![index, element]
                        } else {
                            vec![]
                        }
                    }
                    // receiver → result (and a method call's `this`)
                    (ClassName::HasProp, [receiver, _, determined @ ..]) => {
                        if fixed(receiver) {
                            determined.iter().collect()
                        } else {
                            vec![]
                        }
                    }
                    // the type → what it holds besides nothing
                    (ClassName::Strip, [ty, sigma]) => {
                        if fixed(ty) {
                            vec![sigma]
                        } else {
                            vec![]
                        }
                    }
                    // the operand and the fields before it → the result
                    (ClassName::Spread, [operand, so_far, result]) => {
                        if fixed(operand) && fixed(so_far) {
                            vec![result]
                        } else {
                            vec![]
                        }
                    }
                    // the container → its elements
                    (ClassName::Iterable, [container, element]) => {
                        if fixed(container) {
                            vec![element]
                        } else {
                            vec![]
                        }
                    }
                    (ClassName::Plus, _) => vec![],
                    // Unknown shape: conservatively, any fixed variable
                    // fixes the whole predicate.
                    (_, types) => {
                        if types
                            .iter()
                            .any(|r| r.vars.iter().any(|v| vars.contains(v)))
                        {
                            types.iter().collect()
                        } else {
                            vec![]
                        }
                    }
                };
                let mut add_vars = Vec::new();
                let mut add_pvars = Vec::new();
                for r in determined {
                    add_vars.extend(r.vars.iter().cloned());
                    add_pvars.extend(r.pvars.iter().cloned());
                }
                for v in add_vars {
                    changed |= vars.insert(v);
                }
                for p in add_pvars {
                    changed |= pvars.insert(p);
                }
            }
            if !changed {
                break;
            }
        }
        (vars, pvars)
    }

    /// Debug-build invariant for [`Self::generalize`], derived independently
    /// of [`Self::env_fixed_vars`]: no quantified variable is bound, and none
    /// is reachable from the environment through the substitution (read via
    /// `main_subst`, the other mirror of the substitution).
    #[cfg(debug_assertions)]
    fn debug_check_generalisation(
        &mut self,
        env_free: &crate::infer::EnvFree,
        gen_vars: &[TVarName],
    ) {
        let reachable: std::collections::HashSet<TVarName> = env_free
            .vars
            .iter()
            .flat_map(|v| self.main_subst.apply(&Type::Var(v.clone())).free_vars())
            .collect();
        for v in gen_vars {
            let var = Type::Var(v.clone());
            debug_assert!(
                self.main_subst.apply(&var) == var,
                "generalize quantified {:?}, which is bound",
                v
            );
            debug_assert!(
                !env_free.vars.contains(v) && !reachable.contains(v),
                "generalize quantified {:?}, which the environment reaches",
                v
            );
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
    pub(crate) fn apply_subst_pred(&self, pred: &TypePred) -> TypePred {
        TypePred {
            class: pred.class,
            types: pred.types.iter().map(|t| self.apply_subst(t)).collect(),
            origin: pred.origin,
        }
    }

    /// Check if a type variable occurs in a type (occurs check).
    ///
    /// Walks `ty` through the substitution as it goes, each bound
    /// variable's type once: applying the substitution first copied the
    /// type whole, and a type that shares a large part (a DOM element's
    /// row, reached again through each of its event handlers' events) was
    /// expanded into a tree exponentially larger than itself.
    pub fn occurs_in(&self, var: TVarId, ty: &Type) -> bool {
        let mut seen = std::collections::HashSet::new();
        self.occurs_in_impl(var, ty, &mut seen)
    }

    /// The type a variable is bound to, if it is bound and not yet seen.
    fn bound_unseen(
        &self,
        id: TVarId,
        seen: &mut std::collections::HashSet<TVarId>,
    ) -> Option<&Type> {
        let bound = self.main_subst.get(&TVarName::Flex(id))?;
        seen.insert(id).then_some(bound)
    }

    fn occurs_in_impl(
        &self,
        var: TVarId,
        ty: &Type,
        seen: &mut std::collections::HashSet<TVarId>,
    ) -> bool {
        match ty {
            Type::Number
            | Type::String
            | Type::Boolean
            | Type::Undefined
            | Type::Null
            | Type::Regex
            | Type::NewTarget
            | Type::ArrowThis
            | Type::TypedArray(_)
            | Type::Error => false,

            Type::Var(TVarName::Flex(id)) => {
                *id == var
                    || self
                        .bound_unseen(*id, seen)
                        .is_some_and(|b| self.occurs_in_impl(var, b, seen))
            }
            Type::Var(TVarName::Skolem(_)) => false,

            Type::Func {
                this_type,
                params,
                ret,
            } => {
                this_type
                    .as_ref()
                    .is_some_and(|t| self.occurs_in_impl(var, t, seen))
                    || params.iter().any(|p| self.occurs_in_impl(var, &p.ty, seen))
                    || self.occurs_in_impl(var, ret, seen)
            }

            Type::Row(row) => {
                row.props
                    .values()
                    .any(|e| self.occurs_in_impl(var, &e.ty, seen))
                    || match &row.tail {
                        RowTail::Open(TVarName::Flex(id)) => {
                            *id == var
                                || self
                                    .bound_unseen(*id, seen)
                                    .is_some_and(|b| self.occurs_in_impl(var, b, seen))
                        }
                        RowTail::Recursive(_, args) => {
                            args.iter().any(|a| self.occurs_in_impl(var, a, seen))
                        }
                        _ => false,
                    }
            }

            Type::Array(elem) => self.occurs_in_impl(var, elem, seen),
            Type::Maybe(_, inner) => self.occurs_in_impl(var, inner, seen),
            Type::Promise(inner) => self.occurs_in_impl(var, inner, seen),
            Type::Map(value) => self.occurs_in_impl(var, value, seen),
            Type::Tuple(elems) => elems.iter().any(|e| self.occurs_in_impl(var, e, seen)),

            Type::Named(_, args) => args.iter().any(|a| self.occurs_in_impl(var, a, seen)),

            Type::Literal(_) => false,
            Type::Union(members) => members.iter().any(|m| self.occurs_in_impl(var, m, seen)),

            Type::Module(_) => {
                // A module's exports are schemes; the occurs check looks
                // at free variables of each scheme (i.e. those not bound
                // by the scheme's quantifier).
                let Type::Module(m) = self.apply_subst(ty) else {
                    unreachable!("a module stays one")
                };
                m.exports
                    .values()
                    .any(|scheme| scheme.free_vars().contains(&TVarName::Flex(var)))
            }
        }
    }

    /// Check if a type variable occurs within a row type (for recursive type detection).
    /// Returns true if the variable occurs at the tail position of a row.
    /// (Walks through the substitution lazily, as [`Self::occurs_in`].)
    /// The fields of the row `ty` when it ends in `var` (its tail is
    /// `var`, through the rows, and recursive types' rows, its tail is
    /// bound to): every field on the way, the first of each label. `None`
    /// if it doesn't end in `var` (it ends in another variable, is closed,
    /// or isn't a row).
    ///
    /// Binding `var` to such a row makes no recursive type: a row's tail
    /// stands for the fields it doesn't list, so `ρ = {F | ρ}` says that
    /// `ρ` has the fields `F`, `ρ := {F | ρ'}`, and with no fields says
    /// nothing. (Made one, `μX. {F | X}` is a row that never ends:
    /// unifying it with another row extends that one's tail forever.)
    pub fn row_ends_in(
        &self,
        var: TVarId,
        ty: &Type,
    ) -> Option<std::collections::BTreeMap<crate::types::PropName, crate::types::FieldEntry>> {
        let mut fields = std::collections::BTreeMap::new();
        let mut seen_vars = std::collections::HashSet::new();
        let mut seen_named = std::collections::HashSet::new();
        let mut unrolled: Type;
        let mut cur = ty;
        loop {
            match cur {
                Type::Row(row) => {
                    for (k, e) in &row.props {
                        fields.entry(k.clone()).or_insert_with(|| e.clone());
                    }
                    match &row.tail {
                        RowTail::Open(TVarName::Flex(id)) if *id == var => return Some(fields),
                        RowTail::Open(TVarName::Flex(id)) => {
                            cur = self.bound_unseen(*id, &mut seen_vars)?;
                        }
                        _ => return None,
                    }
                }
                Type::Var(TVarName::Flex(id)) if *id == var => return Some(fields),
                Type::Var(TVarName::Flex(id)) => {
                    cur = self.bound_unseen(*id, &mut seen_vars)?;
                }
                Type::Named(id, args) if !self.is_nominal_type(*id) => {
                    if !seen_named.insert(*id) {
                        return None;
                    }
                    unrolled = self.unroll_named(*id, args)?;
                    cur = &unrolled;
                }
                _ => return None,
            }
        }
    }

    pub fn is_inside_row_type(&self, var: TVarId, ty: &Type) -> bool {
        // A variable's type is looked at once outside a row and once
        // inside one (where finding `var` means more).
        let mut seen = [
            std::collections::HashSet::new(),
            std::collections::HashSet::new(),
        ];
        self.is_inside_row_type_impl(var, ty, false, &mut seen)
    }

    fn is_inside_row_type_impl(
        &self,
        var: TVarId,
        ty: &Type,
        in_row: bool,
        seen: &mut [std::collections::HashSet<TVarId>; 2],
    ) -> bool {
        match ty {
            Type::Row(row) => {
                // Check if var is the row tail (a bound tail continues
                // the row)
                let tail = match &row.tail {
                    RowTail::Open(TVarName::Flex(id)) if *id == var => return true,
                    RowTail::Open(TVarName::Flex(id)) => self
                        .bound_unseen(*id, &mut seen[1])
                        .is_some_and(|b| self.is_inside_row_type_impl(var, b, true, seen)),
                    _ => false,
                };

                // Check inside properties - we're now inside a row
                tail || row
                    .props
                    .values()
                    .any(|e| self.is_inside_row_type_impl(var, &e.ty, true, seen))
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
                    .is_some_and(|t| self.is_inside_row_type_impl(var, t, in_row, seen))
                    || params
                        .iter()
                        .any(|p| self.is_inside_row_type_impl(var, &p.ty, in_row, seen))
                    || self.is_inside_row_type_impl(var, ret, in_row, seen)
            }

            Type::Var(TVarName::Flex(id)) if *id == var => {
                // Found the variable we're looking for
                // This is valid for recursion if we're inside a row
                in_row
            }
            Type::Var(TVarName::Flex(id)) => self
                .bound_unseen(*id, &mut seen[usize::from(in_row)])
                .is_some_and(|b| self.is_inside_row_type_impl(var, b, in_row, seen)),

            Type::Array(elem) | Type::Maybe(_, elem) => {
                self.is_inside_row_type_impl(var, elem, in_row, seen)
            }
            Type::Promise(inner) => self.is_inside_row_type_impl(var, inner, in_row, seen),
            Type::Map(value) => self.is_inside_row_type_impl(var, value, in_row, seen),
            // A recursive type's arguments, as a type written out there
            // would be: `t ~ μ<{c: () => t}>` (an instance whose field
            // holds the factory that made it) is solved by a recursive
            // type, not refused by the occurs check.
            Type::Named(_, args) => args
                .iter()
                .any(|a| self.is_inside_row_type_impl(var, a, in_row, seen)),
            Type::Tuple(elems) => elems
                .iter()
                .any(|e| self.is_inside_row_type_impl(var, e, in_row, seen)),

            _ => false,
        }
    }
}

fn plural(n: usize) -> &'static str {
    if n == 1 {
        ""
    } else {
        "s"
    }
}

/// Whether `err` is a mismatch inside the types compared, at a member
/// of theirs (`UnificationError::member` and the like).
fn names_member(err: &IntyError) -> bool {
    use crate::error::TypeError;
    match err.as_type() {
        Some(
            TypeError::UnificationError { member, .. }
            | TypeError::ThisMismatch { member, .. }
            | TypeError::FieldPresenceMismatch { member, .. },
        ) => member.is_some(),
        _ => false,
    }
}

/// The `this` of a function type, bare or a callable row's call.
fn callable_this(ty: &Type) -> Option<Type> {
    match ty {
        Type::Func {
            this_type: Some(t), ..
        } => Some((**t).clone()),
        Type::Row(row) => row
            .props
            .get(&crate::types::PropName(
                crate::types::CALLABLE_KEY.to_string(),
            ))
            .and_then(|e| callable_this(&e.ty)),
        _ => None,
    }
}

/// How many parameters a function type (or a callable record's call
/// signature) lists.
fn callable_arity(ty: &Type) -> Option<usize> {
    match ty {
        Type::Func { params, .. } => Some(params.len()),
        Type::Row(row) => row
            .props
            .get(&crate::types::PropName(
                crate::types::CALLABLE_KEY.to_string(),
            ))
            .and_then(|e| callable_arity(&e.ty)),
        _ => None,
    }
}

/// A function type (or a callable record) with only its first `n`
/// parameters.
fn with_callable_arity(ty: &Type, n: usize) -> Type {
    match ty {
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type.clone(),
            params: params[..n.min(params.len())].to_vec(),
            ret: ret.clone(),
        },
        Type::Row(row) => {
            let mut row = row.clone();
            let key = crate::types::PropName(crate::types::CALLABLE_KEY.to_string());
            if let Some(e) = row.props.get_mut(&key) {
                e.ty = with_callable_arity(&e.ty, n);
            }
            Type::Row(row)
        }
        _ => ty.clone(),
    }
}

/// A function type with its `this` replaced.
fn with_callable_this(ty: &Type, this: Type) -> Type {
    match ty {
        Type::Func { params, ret, .. } => Type::Func {
            this_type: Some(Box::new(this)),
            params: params.clone(),
            ret: ret.clone(),
        },
        Type::Row(row) => {
            let mut row = row.clone();
            let key = crate::types::PropName(crate::types::CALLABLE_KEY.to_string());
            if let Some(e) = row.props.get_mut(&key) {
                e.ty = with_callable_this(&e.ty, this);
            }
            Type::Row(row)
        }
        _ => ty.clone(),
    }
}

/// At most this many origins are shown for one side of a mismatch.
pub(crate) const MAX_ORIGINS: usize = 6;

/// Sort `origins` by where they are, without repeats, at most
/// [`MAX_ORIGINS`].
pub(crate) fn tidy_origins(origins: &mut Vec<TypeOrigin>) {
    origins.sort_by_key(|o| (o.span().start, o.span().end));
    origins.dedup_by_key(|o| o.span());
    origins.truncate(MAX_ORIGINS);
}

/// A field of an object literal (see `InferState::literal_fields`).
#[derive(Debug, Clone)]
pub(crate) struct LiteralField {
    /// Its member path (`a.b` for `b` in a literal `a` holds).
    pub path: String,
    /// The whole field (`name: value`, or a method).
    pub span: Span,
    /// For a function: whether it reads `this` (a method or a
    /// `function` whose body mentions `this`; an arrow function doesn't).
    pub reads_this: Option<bool>,
}

/// The fields of an object literal, and of the literals its fields hold,
/// in source order.
fn collect_literal_fields(
    properties: &[crate::ast::PropDef],
    prefix: &str,
    out: &mut Vec<LiteralField>,
) {
    use crate::ast::{Expr, PropDef, PropKey};
    let name = |key: &PropKey| match key {
        PropKey::Ident(s) | PropKey::String(s) => s.clone(),
        PropKey::Number(n) => n.to_string(),
    };
    let path = |key: &PropKey| {
        if prefix.is_empty() {
            name(key)
        } else {
            format!("{prefix}.{}", name(key))
        }
    };
    for prop in properties {
        match prop {
            PropDef::Property {
                key, value, span, ..
            } => {
                let path = path(key);
                let reads_this = match value {
                    Expr::Function { arrow: true, .. } => Some(false),
                    Expr::Function { body, .. } => {
                        Some(crate::ast::free_idents::mentions_this_in_stmt(body))
                    }
                    _ => None,
                };
                out.push(LiteralField {
                    path: path.clone(),
                    span: *span,
                    reads_this,
                });
                if let Expr::Object { properties, .. } = value {
                    collect_literal_fields(properties, &path, out);
                }
            }
            PropDef::Method {
                key, body, span, ..
            } => out.push(LiteralField {
                path: path(key),
                span: *span,
                reads_this: Some(crate::ast::free_idents::mentions_this_in_stmt(body)),
            }),
            _ => {}
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
        let r = state.join(span, &Type::Number, &Type::Number).unwrap();
        assert_eq!(r, Type::Number);
    }

    #[test]
    fn test_join_unifiable_types() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let v = Type::flex(0);
        // a flex var joined with Number unifies to Number
        let r = state.join(span, &v, &Type::Number).unwrap();
        assert_eq!(r, Type::Number);
    }

    #[test]
    fn test_join_disjoint_primitives_is_an_error() {
        // Branches don't form an implicit union.
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let err = state.join(span, &Type::Number, &Type::String).unwrap_err();
        assert!(
            err.to_string().contains("Branches have different types"),
            "{}",
            err
        );
    }

    #[test]
    fn test_join_with_null_is_an_error() {
        // No guessed sum (as in the model): `Number | Null` is said.
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        assert!(state.join(span, &Type::Number, &Type::Null).is_err());
        let sum = Type::union([Type::Number, Type::Null]);
        assert_eq!(state.join(span, &sum, &Type::Null).unwrap(), sum);
        assert_eq!(state.join(span, &Type::Number, &sum).unwrap(), sum);
    }

    #[test]
    fn test_union_of_disjoint_primitives_yields_union() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let r = state.union_of(span, &Type::Number, &Type::String);
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
        let r = state
            .join(span, &Type::lit_string("a"), &Type::String)
            .unwrap();
        assert_eq!(r, Type::String);
    }

    #[test]
    fn test_join_literals_widen_to_their_base() {
        let mut state = InferState::new();
        let span = Span::new(0, 0);
        let r = state
            .join(span, &Type::lit_string("a"), &Type::lit_string("b"))
            .unwrap();
        assert_eq!(r, Type::String);
        // `union_of` keeps them distinct (a union of literal arms).
        match state.union_of(span, &Type::lit_string("a"), &Type::lit_string("b")) {
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

/// A method call whose callee's `this` wasn't known at the call (see
/// `InferState::settle_receivers`): its `this`, the receiver, and where.
/// One still unknown when settled is, unless `unknown_is_method`, a
/// function that uses no `this`; if it is, a method of the receiver (a
/// call on a value an importer decided, whose callee was read off it).
#[derive(Debug, Clone)]
pub(crate) struct PendingReceiver {
    pub(crate) this: Type,
    pub(crate) receiver: Type,
    pub(crate) span: Span,
    pub(crate) unknown_is_method: bool,
}
