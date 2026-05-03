//! Type inference module for minfern.
//!
//! This module provides the core type inference implementation:
//! - `state`: Inference state with fresh variable generation and substitution
//! - `env`: Type environment for variable bindings
//! - `unify`: Unification algorithm with occurs check
//! - `features`: Per-feature inference rules (scalars, arrays, rows, …)
//! - `type_parser`: Parser for TypeScript-style type annotations
//! - `decorate`: AST decoration with inferred types

mod decorate;
mod env;
mod features;
mod narrow;
mod state;
mod type_parser;
mod unify;

#[cfg(test)]
mod tests;

pub use decorate::decorate_with_types;
pub use env::TypeEnv;
pub use narrow::{apply_narrowing, Narrowing, Path};
pub use state::{InferConfig, InferState, InferWarning, PendingConstraint, TypeClass};
pub use type_parser::parse_type_annotation;
pub use unify::UnifyResult;

use crate::error::{MinfernError, TypeError};
use crate::parser::ast::{ExportDecl, Expr, Program, Stmt, VarDeclarator, VarKind};
use crate::types::Type;

/// Result type for inference operations.
pub type InferResult<T> = Result<T, MinfernError>;

impl InferState {
    /// Infer the type of a program.
    pub fn infer_program(&mut self, env: &TypeEnv, program: &Program) -> InferResult<Type> {
        let (ty, _env) = self.infer_program_with_env(env, program)?;
        Ok(ty)
    }

    /// Infer the type of a program, returning both the type and the final environment.
    pub fn infer_program_with_env(
        &mut self,
        env: &TypeEnv,
        program: &Program,
    ) -> InferResult<(Type, TypeEnv)> {
        self.infer_stmt_list(env, &program.statements)
    }

    /// Infer a list of statements with function-declaration hoisting.
    ///
    /// Groups adjacent `function` declarations into a single binding group
    /// and processes them together (hoist → infer bodies → generalise) so
    /// mutual recursion and forward references between peers in the same
    /// group type-check correctly. Non-function statements break up the
    /// groups and are inferred in the usual left-to-right order, which
    /// matches JavaScript's evaluation order for anything that isn't a
    /// `function` declaration.
    pub(crate) fn infer_stmt_list(
        &mut self,
        env: &TypeEnv,
        stmts: &[Stmt],
    ) -> InferResult<(Type, TypeEnv)> {
        // Track names declared via `const` in this scope to reject
        // duplicate declarations, which are almost always bugs and match
        // standard JS semantics for const. Synthesised destructuring
        // temps (`$destr$N`) are skipped — they're uniquely generated
        // per pattern and can't collide.
        let mut const_names: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut result = Type::Undefined;
        let mut current_env = env.clone();
        let mut i = 0;
        while i < stmts.len() {
            if matches!(stmts[i], Stmt::FunctionDecl { .. }) {
                // Extend the group across intervening empty statements:
                // `function f() {} ; function g() {}` should still let
                // `f` and `g` see each other (JS hoists all function
                // declarations in a scope to the top). Without this,
                // a stray `;` silently breaks mutual recursion.
                let start = i;
                while i < stmts.len()
                    && matches!(stmts[i], Stmt::FunctionDecl { .. } | Stmt::Empty { .. })
                {
                    i += 1;
                }
                // Trim trailing empties so the slice handed to
                // `infer_function_group` ends on a FunctionDecl — the
                // group-inference routine skips empties either way, but
                // trimming avoids pointless iteration over them.
                let mut end = i;
                while end > start
                    && matches!(stmts[end - 1], Stmt::Empty { .. })
                {
                    end -= 1;
                }
                if end == start {
                    // We only saw empties; fall through to the
                    // regular path so each Empty is processed (sets
                    // `result` to Undefined).
                    i = start;
                } else {
                    current_env = self.infer_function_group(&current_env, &stmts[start..end])?;
                    i = end;
                    continue;
                }
            }
            {
                if let Stmt::Var {
                    kind: VarKind::Const,
                    declarations,
                    ..
                } = &stmts[i]
                {
                    for decl in declarations {
                        if decl.name.starts_with("$destr$") {
                            continue;
                        }
                        if !const_names.insert(decl.name.clone()) {
                            return Err(TypeError::Module {
                                message: format!(
                                    "duplicate declaration of 'const {}' in the same scope",
                                    decl.name
                                ),
                                span: decl.span,
                            }
                            .into());
                        }
                    }
                }
                let (ty, new_env) = self.infer_stmt(&current_env, &stmts[i])?;
                result = ty;
                current_env = new_env;
                i += 1;
            }
        }
        Ok((result, current_env))
    }

    /// Infer the type of an expression.
    pub fn infer_expr(&mut self, env: &TypeEnv, expr: &Expr) -> InferResult<Type> {
        match expr {
            Expr::Lit { value, span } => self.infer_literal(value, *span),

            Expr::Ident { name, span } => {
                if let Some(scheme) = env.lookup(name) {
                    let ty = self.instantiate(scheme);
                    // Record origin for type variables from variable references
                    if let Type::Var(var) = &ty {
                        self.record_origin(
                            var.clone(),
                            crate::error::TypeOrigin::Variable {
                                name: name.clone(),
                                span: *span,
                            },
                        );
                    }
                    Ok(ty)
                } else {
                    Err(TypeError::UndefinedVariable {
                        name: name.clone(),
                        span: *span,
                    }
                    .into())
                }
            }

            Expr::This { span: _ } => {
                // 'this' is looked up like any other variable
                if let Some(scheme) = env.lookup("this") {
                    Ok(self.instantiate(scheme))
                } else {
                    // If 'this' is not in scope, return undefined
                    Ok(Type::Undefined)
                }
            }

            Expr::Array { elements, span } => self.infer_array(env, elements, *span),

            Expr::Object { properties, span } => self.infer_object(env, properties, *span),

            Expr::Function {
                name,
                params,
                body,
                type_annotation,
                span,
            } => self.infer_function(env, name.as_deref(), params, body, type_annotation, *span),

            Expr::Member {
                object,
                property,
                span,
            } => self.infer_member(env, object, property, *span),

            Expr::ComputedMember {
                object,
                property,
                span,
            } => self.infer_computed_member(env, object, property, *span),

            Expr::Call {
                callee,
                arguments,
                span,
            } => self.infer_call(env, callee, arguments, *span),

            Expr::New {
                callee,
                arguments,
                span,
            } => self.infer_new(env, callee, arguments, *span),

            Expr::NewTarget { span: _ } => {
                // new.target is either undefined or a function
                Ok(self.fresh_type_var())
            }

            Expr::Unary { op, argument, span } => self.infer_unary(env, *op, argument, *span),

            Expr::Binary {
                op,
                left,
                right,
                span,
            } => self.infer_binary(env, *op, left, right, *span),

            Expr::Assign {
                op,
                left,
                right,
                span,
            } => self.infer_assign(env, *op, left, right, *span),

            Expr::Conditional {
                test,
                consequent,
                alternate,
                span,
            } => self.infer_conditional(env, test, consequent, alternate, *span),

            Expr::Sequence { expressions, span } => self.infer_sequence(env, expressions, *span),

            Expr::TemplateLiteral {
                quasis: _,
                expressions,
                span,
            } => self.infer_template_literal(env, expressions, *span),
        }
    }

    /// Infer the type of a statement.
    /// Returns the type that the statement "produces" and the updated environment.
    pub fn infer_stmt(&mut self, env: &TypeEnv, stmt: &Stmt) -> InferResult<(Type, TypeEnv)> {
        match stmt {
            Stmt::Block { body, .. } => {
                // Function declarations inside a block are hoisted within
                // the block, so we reuse the same grouping logic the
                // top-level program uses.
                let (result, _inner_env) = self.infer_stmt_list(env, body)?;
                // Block introduces a new scope, so we return the original env
                Ok((result, env.clone()))
            }

            Stmt::Empty { .. } => Ok((Type::Undefined, env.clone())),

            Stmt::Expr { expression, .. } => {
                let ty = self.infer_expr(env, expression)?;
                Ok((ty, env.clone()))
            }

            Stmt::Var {
                kind, declarations, ..
            } => self.infer_stmt_var(env, *kind, declarations),

            // Import and export are handled at the module level, not during inference
            // For now, we just skip them (module system is not yet implemented)
            Stmt::Import { .. } => {
                // TODO: Implement module resolution and import type bindings
                Ok((Type::Undefined, env.clone()))
            }

            Stmt::Export { declaration, span } => {
                // Desugar to the underlying declaration and infer that, so
                // `export var x = 1;` and `export function f() {}` end up
                // in the env exactly like their un-exported counterparts.
                // The module resolver reads the final env back out.
                let _ = span;
                match declaration {
                    ExportDecl::Var {
                        kind,
                        declarations,
                        span,
                    } => self.infer_stmt(
                        env,
                        &Stmt::Var {
                            kind: *kind,
                            declarations: declarations.clone(),
                            span: *span,
                        },
                    ),
                    ExportDecl::Function {
                        name,
                        params,
                        body,
                        type_annotation,
                        span,
                    } => self.infer_stmt(
                        env,
                        &Stmt::FunctionDecl {
                            name: name.clone(),
                            params: params.clone(),
                            body: body.clone(),
                            type_annotation: type_annotation.clone(),
                            span: *span,
                        },
                    ),
                    ExportDecl::List { specifiers, span: _ } => {
                        // `export { a, b as c };` doesn't change types — the
                        // resolver reads the exported names from a separate
                        // table built by `modules::collect_exports`. All we
                        // do here is verify each `local` is in fact declared,
                        // so a typo doesn't survive until import time.
                        for spec in specifiers {
                            if env.lookup(&spec.local).is_none() {
                                return Err(MinfernError::Type(TypeError::Module {
                                    message: format!(
                                        "exported name `{}` is not declared in this module",
                                        spec.local
                                    ),
                                    span: spec.span,
                                }));
                            }
                        }
                        Ok((Type::Undefined, env.clone()))
                    }
                    ExportDecl::Default { value, span } => {
                        // `export default function f() { … }` is two bindings:
                        // a function declaration `f` and an alias `default = f`.
                        // Other RHS forms desugar to `const default = <value>;`.
                        if let Expr::Function {
                            name: Some(fn_name),
                            params,
                            body,
                            type_annotation,
                            span: f_span,
                        } = value
                        {
                            let (_, env_after_fn) = self.infer_stmt(
                                env,
                                &Stmt::FunctionDecl {
                                    name: fn_name.clone(),
                                    params: params.clone(),
                                    body: body.clone(),
                                    type_annotation: type_annotation.clone(),
                                    span: *f_span,
                                },
                            )?;
                            let scheme = env_after_fn
                                .lookup(fn_name)
                                .cloned()
                                .expect("function decl should bind its name");
                            Ok((
                                Type::Undefined,
                                env_after_fn.extend("default".to_string(), scheme),
                            ))
                        } else {
                            self.infer_stmt(
                                env,
                                &Stmt::Var {
                                    kind: VarKind::Const,
                                    declarations: vec![VarDeclarator {
                                        name: "default".to_string(),
                                        init: Some(value.clone()),
                                        type_annotation: None,
                                        kind: VarKind::Const,
                                        span: *span,
                                    }],
                                    span: *span,
                                },
                            )
                        }
                    }
                }
            }

            Stmt::If {
                test,
                consequent,
                alternate,
                span,
            } => self.infer_stmt_if(env, test, consequent, alternate, *span),

            Stmt::While { test, body, .. } => self.infer_stmt_while(env, test, body),

            Stmt::DoWhile { body, test, .. } => self.infer_stmt_do_while(env, body, test),

            Stmt::For {
                init,
                test,
                update,
                body,
                ..
            } => self.infer_stmt_for(env, init, test, update, body),

            Stmt::ForIn {
                left,
                right,
                body,
                span,
            } => self.infer_stmt_for_in(env, left, right, body, *span),

            Stmt::ForOf {
                left,
                right,
                body,
                span,
            } => self.infer_stmt_for_of(env, left, right, body, *span),

            Stmt::Break { .. } | Stmt::Continue { .. } => Ok((Type::Undefined, env.clone())),

            Stmt::Return { argument, span: _ } => {
                let ret_type = if let Some(expr) = argument {
                    self.infer_expr(env, expr)?
                } else {
                    Type::Undefined
                };
                Ok((ret_type, env.clone()))
            }

            Stmt::Throw { argument, .. } => {
                let _throw_type = self.infer_expr(env, argument)?;
                // throw doesn't really have a type, but we use Undefined
                Ok((Type::Undefined, env.clone()))
            }

            Stmt::Try {
                block,
                handler,
                finalizer,
                span: _,
            } => self.infer_stmt_try(env, block, handler, finalizer),

            Stmt::Switch {
                discriminant,
                cases,
                span,
            } => self.infer_stmt_switch(env, discriminant, cases, *span),

            Stmt::Labeled { body, .. } => self.infer_stmt(env, body),

            Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation,
                span,
            } => self.infer_stmt_function_decl(env, name, params, body, type_annotation, *span),
        }
    }
}
