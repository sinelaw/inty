//! Variable bindings: declarations, assignment, value restriction.

use std::collections::HashSet;

use crate::error::TypeError;
use crate::span::Span;
use crate::ast::{AssignOp, Expr, PropDef, VarDeclarator, VarKind};
use crate::types::{PropName, TVarName, Type, TypePred, TypeScheme};

use super::super::env::{Mutability, TypeEnv};
use super::super::state::InferState;
use super::super::type_parser::parse_type_annotation_with_pvars;
use super::super::InferResult;

/// If `lhs` is an assignment target whose binding resolves to a polymorphic
/// scheme, return that scheme. Used by `infer_assign` to drive a subsumption
/// check (skolemize-and-unify) on the RHS.
///
/// Returns `Some` for:
/// - `Expr::Ident` whose binding's scheme has bound type variables.
/// - `Expr::Member` `name.prop` where `name`'s scheme is polymorphic *and*
///   `prop`'s field type uses at least one of the scheme's bound variables —
///   in which case the field's polytype is the field type quantified over
///   exactly those variables.
///
/// Returns `None` for monomorphic targets (existing unification path is
/// sufficient) and for LHS shapes we don't model (computed members, deeply
/// nested members, etc.) — those fall back to the existing path.
fn lhs_polytype(env: &TypeEnv, lhs: &Expr) -> Option<TypeScheme> {
    match lhs {
        Expr::Ident { name, .. } => {
            let scheme = env.lookup(name)?;
            if scheme.vars.is_empty() {
                None
            } else {
                Some(scheme.clone())
            }
        }
        Expr::Member { .. } => {
            // Walk the member chain to the root identifier, collecting the
            // property path in source order. Handles arbitrarily nested
            // LHSs like `obj.a.b.f = ...` so a polytype living several
            // levels deep can't slip past the subsumption check.
            let mut path: Vec<&str> = Vec::new();
            let mut cur = lhs;
            let root_name = loop {
                match cur {
                    Expr::Ident { name, .. } => break name,
                    Expr::Member {
                        object, property, ..
                    } => {
                        path.push(property);
                        cur = object.as_ref();
                    }
                    _ => return None,
                }
            };
            path.reverse();

            let obj_scheme = env.lookup(root_name)?;
            if obj_scheme.vars.is_empty() {
                return None;
            }
            let mut cur_ty = &obj_scheme.body.ty;
            for prop in &path {
                let row = match cur_ty {
                    Type::Row(row) => row,
                    _ => return None,
                };
                let prop_key = PropName((*prop).to_string());
                cur_ty = &row.props.get(&prop_key)?.ty;
            }
            let field_ty = cur_ty.clone();
            let field_free = field_ty.free_vars();
            let mut field_vars: Vec<TVarName> = obj_scheme
                .vars
                .iter()
                .filter(|v| field_free.contains(v))
                .cloned()
                .collect();
            field_vars.sort_by_key(|v| v.id());
            if field_vars.is_empty() {
                return None;
            }
            let field_var_set: HashSet<TVarName> = field_vars.iter().cloned().collect();
            let preds: Vec<TypePred> = obj_scheme
                .body
                .preds
                .iter()
                .filter(|p| p.free_vars().iter().any(|v| field_var_set.contains(v)))
                .cloned()
                .collect();
            Some(TypeScheme::qualified(field_vars, preds, field_ty))
        }
        _ => None,
    }
}

/// Check if an expression is a syntactic value (for the value restriction).
///
/// Syntactic values can be safely generalized because they don't perform
/// any computation that could create mutable state with polymorphic type.
fn is_syntactic_value(expr: &Expr) -> bool {
    match expr {
        // Literals are values
        Expr::Lit { .. } => true,

        // Variables are values
        Expr::Ident { .. } => true,

        // `this` is a value
        Expr::This { .. } => true,

        // Functions are values
        Expr::Function { .. } => true,

        // Array literals are values if all elements are values
        Expr::Array { elements, .. } => elements
            .iter()
            .all(|e| e.as_ref().map_or(true, is_syntactic_value)),

        // Object literals are values if all property values are values
        Expr::Object { properties, .. } => properties.iter().all(|p| match p {
            PropDef::Property { value, .. } => is_syntactic_value(value),
            // Getters/setters/methods are function-like, so they're values
            PropDef::Getter { .. } | PropDef::Setter { .. } | PropDef::Method { .. } => true,
            // A spread is a value iff its argument is — the merge
            // itself is pure (no side effects beyond evaluating the
            // operand).
            PropDef::Spread { argument, .. } => is_syntactic_value(argument),
        }),

        // A spread's value-ness is the spread argument's value-ness.
        // (Reachable only when a spread expression is bound directly,
        // which the inference rules reject; covered for completeness
        // so the value-restriction predicate is total.)
        Expr::Spread { argument, .. } => is_syntactic_value(argument),

        // Unary operations on values are values (e.g., -1, !true)
        Expr::Unary { argument, .. } => is_syntactic_value(argument),

        // Template literals are values if all expressions are values
        Expr::TemplateLiteral { expressions, .. } => expressions.iter().all(is_syntactic_value),

        // Everything else is NOT a syntactic value:
        // - Function calls
        // - Member access
        // - Binary operations (could have side effects)
        // - Assignments
        // - etc.
        _ => false,
    }
}

/// Check if an expression is a mutable container literal.
///
/// Mutable containers (arrays and objects) should not be generalized when
/// assigned to mutable (`var`) variables because their contents can be
/// mutated through indexing (e.g., `arr[i] = ...`), which would break
/// the polymorphic type by requiring all uses to share the same element type.
///
/// Functions, while syntactic values, are NOT mutable containers because
/// their "contents" (code) cannot be mutated at runtime.
fn is_mutable_container_literal(expr: &Expr) -> bool {
    match expr {
        // Array literals are mutable containers
        Expr::Array { .. } => true,

        // Object literals are mutable containers
        Expr::Object { .. } => true,

        // Everything else is not a mutable container
        // (functions, literals, identifiers, etc.)
        _ => false,
    }
}

impl InferState {
    /// Check if an assignment target is valid (not an immutable binding or polymorphic property).
    pub(in crate::infer) fn check_assignment_target(
        &self,
        env: &TypeEnv,
        left: &Expr,
        span: Span,
    ) -> InferResult<()> {
        match left {
            // Direct assignment to a variable
            Expr::Ident { name, .. } => {
                if let Some(binding) = env.lookup_binding(name) {
                    if binding.mutability == Mutability::Immutable {
                        return Err(TypeError::AssignmentToConstant {
                            name: name.clone(),
                            span,
                        }
                        .into());
                    }
                }
            }

            // Property assignment: obj.prop = ...
            //
            // Writes through polymorphic record fields used to be rejected
            // unconditionally for immutable bindings here. Under the rank-N
            // annotation rule (polytypes only via explicit annotation; see
            // `infer_stmt_var`) plus the subsumption check in `infer_assign`,
            // those writes are now checked against the field's declared
            // polytype instead, so the rejection is no longer needed.
            //
            // TODO(modules): if the object's scheme body is `Type::Module(_)`,
            // reject every property assignment unconditionally with a
            // dedicated "cannot assign to module export" error. ESM
            // bindings are immutable on the importer side; today the
            // assignment falls through and tends to fail later as a
            // unification mismatch instead of a clean diagnostic.
            Expr::Member { .. } => {}

            // Computed property assignment: obj[expr] = ...
            // We don't check this because we can't statically determine the property
            Expr::ComputedMember { .. } => {}

            // Other expressions (destructuring, etc.) - no special checks
            _ => {}
        }

        Ok(())
    }

    /// Infer the type of an assignment.
    pub(in crate::infer) fn infer_assign(
        &mut self,
        env: &TypeEnv,
        op: AssignOp,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        // Check for assignment to immutable bindings
        self.check_assignment_target(env, left, span)?;

        let right_type = self.infer_expr(env, right)?;

        // Subsumption check: if the LHS resolves to a polymorphic scheme
        // (a polymorphic var, or a polymorphic property of a polymorphic
        // record), the RHS must be at-least-as-polymorphic. We enforce
        // this by *skolemizing* the binding's polytype and unifying the
        // resulting rigid type with the RHS. Assigning a less-polymorphic
        // value fails because skolems only unify with themselves — see
        // unify.rs:96 for the rule. Without this, reassignment silently
        // pins fresh-instantiated copies of the polytype while the
        // binding's stored scheme stays unchanged, so later uses
        // re-instantiate at the original (now-stale) polymorphism and
        // produce inferred types that disagree with runtime values.
        // Logical-assignment ops (`??=`, `&&=`, `||=`) constrain LHS and
        // RHS to the same type just like plain `=` — the only runtime
        // difference is short-circuiting on the LHS test, which doesn't
        // affect typing. Route them through the same polytype
        // skolemize/escape path that `=` uses.
        if matches!(
            op,
            AssignOp::Assign
                | AssignOp::NullishAssign
                | AssignOp::LogicalAndAssign
                | AssignOp::LogicalOrAssign
        ) {
            if let Some(expected) = lhs_polytype(env, left) {
                let env_free_before = env.free_vars();
                let (skolems, expected_ty) = self.skolemize(&expected);
                self.unify(span, &expected_ty, &right_type)?;
                // Skolem escape check (Peyton Jones et al. 2007 §4
                // "checkSigma"): if any of our fresh skolems leaked into a
                // flex var that was free in the env before this check,
                // the RHS would have constrained an outer binding to the
                // skolemized form of x's polytype. Reject — the assignment
                // isn't truly polymorphic.
                if !skolems.is_empty() {
                    let skolem_set: HashSet<TVarName> = skolems.into_iter().collect();
                    for v in &env_free_before {
                        if !v.is_flex() {
                            continue;
                        }
                        let after = self.zonk(&Type::Var(v.clone()));
                        if after.free_vars().iter().any(|s| skolem_set.contains(s)) {
                            return Err(TypeError::EscapedSkolem { span }.into());
                        }
                    }
                }
                return Ok(self.zonk(&expected_ty));
            }
        }

        let left_type = self.infer_expr(env, left)?;

        match op {
            AssignOp::Assign
            | AssignOp::NullishAssign
            | AssignOp::LogicalAndAssign
            | AssignOp::LogicalOrAssign => {
                // RHS subsumes into LHS: the LHS already has its
                // declared/widened type, the RHS is whatever the
                // right expression synthesised. `Lit ≤ Base` lets a
                // string literal flow into a `String`-typed binding.
                //
                // Special case: when the LHS is still an unbound flex
                // variable (e.g. `var x;` then later `x = 42`), this
                // assignment is effectively the binding's first
                // initialisation. Widen the RHS so the variable lands
                // on its base type, matching what `var x = 42` would
                // give.
                //
                // The short-circuit ops (`??=`, `&&=`, `||=`) share
                // this rule: at the type level they look identical to
                // `=`, the runtime test only decides whether the
                // assignment actually fires.
                let lhs_resolved = self.zonk(&left_type);
                let rhs_for_assign = if matches!(
                    lhs_resolved,
                    Type::Var(crate::types::TVarName::Flex(_))
                ) {
                    right_type.widen_fresh_literals()
                } else {
                    right_type.clone()
                };
                self.subsume(span, &rhs_for_assign, &left_type)?;
            }

            AssignOp::AddAssign => {
                // Like +: widen operands so `n += 1` doesn't get
                // pinned to a singleton type.
                let left_widened = left_type.widen_fresh_literals();
                let right_widened = right_type.widen_fresh_literals();
                let result = self.fresh_type_var();
                self.add_constraint(TypePred::plus(result.clone()), span);
                self.subsume(span, &left_widened, &result)?;
                self.subsume(span, &right_widened, &result)?;
            }

            AssignOp::SubAssign
            | AssignOp::MulAssign
            | AssignOp::DivAssign
            | AssignOp::ModAssign
            | AssignOp::PowAssign => {
                self.subsume(span, &left_type, &Type::Number)?;
                self.subsume(span, &right_type, &Type::Number)?;
            }

            AssignOp::LShiftAssign
            | AssignOp::RShiftAssign
            | AssignOp::URShiftAssign
            | AssignOp::BitAndAssign
            | AssignOp::BitOrAssign
            | AssignOp::BitXorAssign => {
                self.subsume(span, &left_type, &Type::Number)?;
                self.subsume(span, &right_type, &Type::Number)?;
            }
        }

        Ok(self.zonk(&left_type))
    }

    /// Handle a `var` / `let` / `const` declaration statement.
    pub(in crate::infer) fn infer_stmt_var(
        &mut self,
        env: &TypeEnv,
        kind: VarKind,
        declarations: &[VarDeclarator],
    ) -> InferResult<(Type, TypeEnv)> {
        let mut new_env = env.clone();

        for decl in declarations {
            // Check if this is a declaration (no init, with type annotation)
            let is_declaration = decl.init.is_none() && decl.type_annotation.is_some();

            // Parse the annotation up-front (if any) so we can use it
            // as the *expected* type when checking the initialiser
            // bidirectionally — that's how an object-literal RHS can
            // keep its singleton field types when the annotation
            // pins them.
            let annotated_type: Option<(Type, Span)> = if let Some(annotation) = &decl.type_annotation {
                let annotation_span = Span::new(annotation.span.start, annotation.span.end);
                let (ann_ty, var_map, next_pvar) = parse_type_annotation_with_pvars(
                    &annotation.content,
                    annotation_span,
                    self.next_var_id(),
                    self.next_pvar_id(),
                    &self.type_aliases,
                )?;
                self.bump_pvar_id_to(next_pvar);
                if let Some(&max) = var_map.values().max() {
                    self.bump_var_id_to(max + 1);
                }
                Some((ann_ty, annotation_span))
            } else {
                None
            };

            let var_type = match (&decl.init, &annotated_type) {
                (Some(init), Some((ann_ty, _))) => {
                    // Bidirectional check: pushes the annotation into
                    // the initialiser so e.g. an object literal's
                    // primitive fields keep their singleton types
                    // when the annotation asks for them.
                    self.check_expr(&new_env, init, ann_ty)?
                }
                (Some(init), None) => self.infer_expr(&new_env, init)?,
                (None, _) => self.fresh_type_var(),
            };

            // If there was an annotation, the annotation governs the
            // resulting type. Otherwise apply fresh-literal widening:
            // `var k = "circle"` becomes `k : String`, not
            // `k : "circle"`. The annotation is the escape hatch when
            // the user wants to keep the singleton type.
            let var_type = if let Some((ann_ty, ann_span)) = annotated_type {
                // The check_expr above already enforced the
                // subsumption when an init was present; for
                // declaration-only forms we still need a sanity
                // subsume against the fresh var (no-op here, but
                // keeps the same diagnostic flow).
                if decl.init.is_none() {
                    self.subsume(ann_span, &var_type, &ann_ty)?;
                }
                self.zonk(&ann_ty)
            } else {
                var_type.widen_fresh_literals()
            };

            // Record the type for this declaration
            self.record_decl_type(decl.span, var_type.clone());

            // Determine if we should generalize:
            // 1. Declarations (no init, with type annotation) are always
            //    generalized because they represent external bindings whose
            //    polytype is explicitly stated. Writes through annotated
            //    polymorphic record fields are then subsumption-checked at
            //    the assignment site (see `infer_assign`).
            // 2. Definitions with syntactic-value initializers are generalized
            //    EXCEPT for mutable container literals (arrays, object
            //    literals), regardless of var/let/const. Container fields and
            //    elements can be mutated via aliasing — e.g.
            //    `var alias = c; alias.f = ...` writes through to `c` — so
            //    giving them a polytype lets writes silently violate the
            //    polymorphism. Polymorphic record/array storage must be
            //    opted in via an explicit type annotation (case 1).
            let scheme = if is_declaration {
                let env_free = new_env.free_vars();
                self.generalize(&env_free, &var_type)
            } else {
                match &decl.init {
                    Some(init)
                        if is_syntactic_value(init)
                            && (self.config.generalize_mutable_var_containers
                                || !is_mutable_container_literal(init)) =>
                    {
                        let env_free = new_env.free_vars();
                        self.generalize(&env_free, &var_type)
                    }
                    _ => TypeScheme::mono(var_type),
                }
            };

            // Determine mutability:
            // 1. const declarations are always immutable
            // 2. Declarations (no init, with type annotation) are immutable
            //    (per the design doc, they represent external APIs)
            // 3. var declarations with init are mutable
            let mutability = match kind {
                VarKind::Const => Mutability::Immutable,
                VarKind::Var | VarKind::Let if is_declaration => Mutability::Immutable,
                VarKind::Var | VarKind::Let => Mutability::Mutable,
            };
            // Also persist the generalised scheme so LSP/inlay hints
            // can recover predicates after the scope is gone.
            self.record_decl_scheme(decl.span, scheme.clone());
            new_env = new_env.extend_with_mutability(decl.name.clone(), scheme, mutability);
        }

        Ok((Type::Undefined, new_env))
    }
}
