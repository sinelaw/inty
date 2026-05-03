//! Conditional/sequence expressions and control-flow statements.

use crate::lexer::Span;
use crate::parser::ast::{CatchClause, Expr, ForInLhs, ForInit, Stmt, SwitchCase, VarDeclarator};
use crate::types::{Type, TypeScheme};

use super::super::env::TypeEnv;
use super::super::narrow::{apply_narrowing, try_extract_narrowing};
use super::super::state::InferState;
use super::super::InferResult;

/// If `ty` is a closed union whose every member is a literal type
/// (or just a single literal type), return the set of literal values.
/// Otherwise None.
fn literal_set_of_type(ty: &Type) -> Option<Vec<crate::types::LitValue>> {
    match ty {
        Type::Literal(l) => Some(vec![l.clone()]),
        Type::Union(members) => {
            let mut out = Vec::with_capacity(members.len());
            for m in members {
                if let Type::Literal(l) = m {
                    out.push(l.clone());
                } else {
                    return None;
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// Format a literal value for human-readable warning messages.
fn format_literal(l: &crate::types::LitValue) -> String {
    match l {
        crate::types::LitValue::String(s) => format!("\"{}\"", s),
        crate::types::LitValue::Number(n) => n.to_string(),
        crate::types::LitValue::Bool(b) => b.to_string(),
    }
}

impl InferState {
    /// Infer the type of a conditional expression.
    pub(in crate::infer) fn infer_conditional(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        consequent: &Expr,
        alternate: &Expr,
        span: Span,
    ) -> InferResult<Type> {
        let _test_type = self.infer_expr(env, test)?;

        // Flow-sensitive narrowing: if the test is one of the recognised
        // patterns (typeof / === / !==), refine the consequent's env with
        // the predicate and the alternate's env with its negation.
        let (cons_env, alt_env) = match try_extract_narrowing(test) {
            Some((path, narrowing)) => (
                apply_narrowing(self, env, &path, &narrowing),
                apply_narrowing(self, env, &path, &narrowing.negate()),
            ),
            None => (env.clone(), env.clone()),
        };

        let cons_type = self.infer_expr(&cons_env, consequent)?;
        let alt_type = self.infer_expr(&alt_env, alternate)?;

        // Branches that disagree in type are merged into a union rather
        // than rejected — see InferState::join for details.
        Ok(self.join(span, &cons_type, &alt_type))
    }

    /// Infer the type of a sequence expression.
    pub(in crate::infer) fn infer_sequence(
        &mut self,
        env: &TypeEnv,
        expressions: &[Expr],
        _span: Span,
    ) -> InferResult<Type> {
        let mut result = Type::Undefined;
        for expr in expressions {
            result = self.infer_expr(env, expr)?;
        }
        Ok(result)
    }

    /// If the discriminant of a switch has a finite, closed type (a
    /// union of literal types, or a single literal type), return the
    /// covered literals; used by switch-exhaustiveness analysis.
    ///
    /// We rely on phase-3 union elimination having already pushed
    /// member access through unions, so `shape.kind` on a discriminated
    /// union resolves to a literal union directly.
    fn resolve_finite_literal_set(
        &self,
        _discriminant: &Expr,
        disc_type: &Type,
    ) -> Option<Vec<crate::types::LitValue>> {
        let disc = self.apply_subst(disc_type);
        literal_set_of_type(&disc)
    }

    /// Bind a list of `for`-init declarators into the loop env.
    fn bind_for_init_decls(&mut self, env: &TypeEnv, decls: &[VarDeclarator]) -> InferResult<TypeEnv> {
        let mut new_env = env.clone();
        for decl in decls {
            let var_type = if let Some(init_expr) = &decl.init {
                self.infer_expr(&new_env, init_expr)?
            } else {
                self.fresh_type_var()
            };
            // Record the type for this declaration
            self.record_decl_type(decl.span, var_type.clone());
            new_env = new_env.extend(decl.name.clone(), TypeScheme::mono(var_type));
        }
        Ok(new_env)
    }

    /// Handle an `if` statement.
    pub(in crate::infer) fn infer_stmt_if(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        consequent: &Stmt,
        alternate: &Option<Box<Stmt>>,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let _test_type = self.infer_expr(env, test)?;

        let (cons_env, alt_env) = match try_extract_narrowing(test) {
            Some((path, narrowing)) => (
                apply_narrowing(self, env, &path, &narrowing),
                apply_narrowing(self, env, &path, &narrowing.negate()),
            ),
            None => (env.clone(), env.clone()),
        };

        let (cons_type, _) = self.infer_stmt(&cons_env, consequent)?;

        let result = if let Some(alt) = alternate {
            let (alt_type, _) = self.infer_stmt(&alt_env, alt)?;
            self.join(span, &cons_type, &alt_type)
        } else {
            self.apply_subst(&cons_type)
        };

        Ok((result, env.clone()))
    }

    /// Handle a `while` statement.
    pub(in crate::infer) fn infer_stmt_while(
        &mut self,
        env: &TypeEnv,
        test: &Expr,
        body: &Stmt,
    ) -> InferResult<(Type, TypeEnv)> {
        let _test_type = self.infer_expr(env, test)?;
        self.infer_stmt(env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `do { } while` statement.
    pub(in crate::infer) fn infer_stmt_do_while(
        &mut self,
        env: &TypeEnv,
        body: &Stmt,
        test: &Expr,
    ) -> InferResult<(Type, TypeEnv)> {
        self.infer_stmt(env, body)?;
        let _test_type = self.infer_expr(env, test)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a C-style `for` statement.
    pub(in crate::infer) fn infer_stmt_for(
        &mut self,
        env: &TypeEnv,
        init: &Option<ForInit>,
        test: &Option<Expr>,
        update: &Option<Expr>,
        body: &Stmt,
    ) -> InferResult<(Type, TypeEnv)> {
        let loop_env = if let Some(init) = init {
            match init {
                ForInit::VarDecl(decls) => self.bind_for_init_decls(env, decls)?,
                ForInit::Expr(expr) => {
                    self.infer_expr(env, expr)?;
                    env.clone()
                }
            }
        } else {
            env.clone()
        };

        if let Some(test) = test {
            self.infer_expr(&loop_env, test)?;
        }

        if let Some(update) = update {
            self.infer_expr(&loop_env, update)?;
        }

        self.infer_stmt(&loop_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `for-in` statement.
    pub(in crate::infer) fn infer_stmt_for_in(
        &mut self,
        env: &TypeEnv,
        left: &ForInLhs,
        right: &Expr,
        body: &Stmt,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let _right_type = self.infer_expr(env, right)?;

        let loop_env = match left {
            ForInLhs::VarDecl(name, _, decl_span) => {
                // for-in iterates over string keys
                let var_type = Type::String;
                self.record_decl_type(*decl_span, var_type.clone());
                env.extend(name.clone(), TypeScheme::mono(var_type))
            }
            ForInLhs::Expr(expr) => {
                let lhs_type = self.infer_expr(env, expr)?;
                self.unify(span, &lhs_type, &Type::String)?;
                env.clone()
            }
        };

        self.infer_stmt(&loop_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `for-of` statement.
    pub(in crate::infer) fn infer_stmt_for_of(
        &mut self,
        env: &TypeEnv,
        left: &ForInLhs,
        right: &Expr,
        body: &Stmt,
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let right_type = self.infer_expr(env, right)?;

        // Right side should be an array
        let elem_type = self.fresh_type_var();
        self.unify(span, &right_type, &Type::array(elem_type.clone()))?;

        let loop_env = match left {
            ForInLhs::VarDecl(name, _, decl_span) => {
                let var_type = self.apply_subst(&elem_type);
                self.record_decl_type(*decl_span, var_type.clone());
                env.extend(name.clone(), TypeScheme::mono(var_type))
            }
            ForInLhs::Expr(expr) => {
                let lhs_type = self.infer_expr(env, expr)?;
                self.unify(span, &lhs_type, &elem_type)?;
                env.clone()
            }
        };

        self.infer_stmt(&loop_env, body)?;
        Ok((Type::Undefined, env.clone()))
    }

    /// Handle a `try / catch / finally` statement.
    pub(in crate::infer) fn infer_stmt_try(
        &mut self,
        env: &TypeEnv,
        block: &Stmt,
        handler: &Option<CatchClause>,
        finalizer: &Option<Box<Stmt>>,
    ) -> InferResult<(Type, TypeEnv)> {
        let (try_type, _) = self.infer_stmt(env, block)?;

        if let Some(catch) = handler {
            // Catch parameter is typed as any (Error in practice)
            let catch_env =
                env.extend(catch.param.clone(), TypeScheme::mono(self.fresh_type_var()));
            self.infer_stmt(&catch_env, &catch.body)?;
        }

        if let Some(finally) = finalizer {
            self.infer_stmt(env, finally)?;
        }

        Ok((try_type, env.clone()))
    }

    /// Handle a `switch` statement.
    pub(in crate::infer) fn infer_stmt_switch(
        &mut self,
        env: &TypeEnv,
        discriminant: &Expr,
        cases: &[SwitchCase],
        span: Span,
    ) -> InferResult<(Type, TypeEnv)> {
        let disc_type = self.infer_expr(env, discriminant)?;

        // The path the switch is dispatching on (if it's an
        // identifier or member chain). Used to narrow each case
        // body's env. Falls back to no narrowing for switches on
        // arbitrary expressions.
        let disc_path = super::super::narrow::path_from_expr(discriminant);

        let mut covered_literals: Vec<crate::types::LitValue> = Vec::new();
        let mut has_default = false;

        for case in cases {
            let case_env = if let Some(test) = &case.test {
                let test_type = self.infer_expr(env, test)?;
                self.unify(span, &disc_type, &test_type)?;

                // If the case test is a literal and we know the
                // discriminator's path, the case body gets an env
                // narrowed by `disc === literal`.
                let lit = super::super::narrow::literal_value_of(test);
                if let Some(lit) = lit.clone() {
                    covered_literals.push(lit);
                }
                match (disc_path.as_ref(), lit) {
                    (Some(path), Some(lit)) => apply_narrowing(
                        self,
                        env,
                        path,
                        &super::super::narrow::Narrowing::Equals(lit),
                    ),
                    _ => env.clone(),
                }
            } else {
                has_default = true;
                env.clone()
            };

            for stmt in &case.consequent {
                self.infer_stmt(&case_env, stmt)?;
            }
        }

        // Phase 6 — exhaustiveness: if the discriminant resolves
        // to a closed union of literal types (after narrowing
        // through subst, which also walks through the path), and
        // the switch has no default, every literal in the union
        // must be covered by some case test. Otherwise we warn.
        // Suppressed when `config.exhaustiveness_warnings` is off.
        if !has_default && self.config.exhaustiveness_warnings {
            let disc_finite = self.resolve_finite_literal_set(discriminant, &disc_type);
            if let Some(domain) = disc_finite {
                let missing: Vec<&crate::types::LitValue> = domain
                    .iter()
                    .filter(|d| !covered_literals.contains(d))
                    .collect();
                if !missing.is_empty() {
                    let names: Vec<String> = missing.iter().map(|l| format_literal(l)).collect();
                    self.warn(
                        span,
                        format!(
                            "non-exhaustive switch: missing case(s) for {}",
                            names.join(", ")
                        ),
                    );
                }
            }
        }

        Ok((Type::Undefined, env.clone()))
    }
}
