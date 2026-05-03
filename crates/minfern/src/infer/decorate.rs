//! AST decoration with inferred types.
//!
//! After type inference, this module walks the AST and adds type annotations
//! showing the inferred types for variables and functions.

use std::collections::HashSet;

use crate::lexer::Span;
use crate::parser::ast::*;
use crate::types::{PrettyContext, QualType, TVarName, Type, TypePred, TypeScheme};

use super::env::TypeEnv;
use super::state::InferState;

/// Collect all this_type variables that are hidden in display.
/// The pretty printer hides this_type when it's a Var, so we shouldn't
/// quantify over these variables in the type signature.
fn collect_hidden_this_vars(ty: &Type) -> HashSet<TVarName> {
    let mut hidden = HashSet::new();
    collect_hidden_this_vars_impl(ty, &mut hidden);
    hidden
}

fn collect_hidden_this_vars_impl(ty: &Type, hidden: &mut HashSet<TVarName>) {
    match ty {
        Type::Func {
            this_type,
            params,
            ret,
        } => {
            // If this_type is a Var, it's hidden in display
            if let Some(t) = this_type {
                if let Type::Var(v) = t.as_ref() {
                    hidden.insert(v.clone());
                }
                collect_hidden_this_vars_impl(t, hidden);
            }
            // Recurse into parameters and return type
            for param in params {
                collect_hidden_this_vars_impl(param, hidden);
            }
            collect_hidden_this_vars_impl(ret, hidden);
        }
        Type::Array(elem) => {
            collect_hidden_this_vars_impl(elem, hidden);
        }
        Type::Promise(inner) => {
            collect_hidden_this_vars_impl(inner, hidden);
        }
        Type::Map(value) => {
            collect_hidden_this_vars_impl(value, hidden);
        }
        Type::Row(row) => {
            for prop_ty in row.props.values() {
                collect_hidden_this_vars_impl(prop_ty, hidden);
            }
        }
        _ => {}
    }
}

/// Decorate an AST with inferred type annotations.
pub struct Decorator<'a> {
    state: &'a InferState,
    ctx: PrettyContext,
}

impl<'a> Decorator<'a> {
    pub fn new(state: &'a InferState) -> Self {
        Self {
            state,
            ctx: PrettyContext::new(),
        }
    }

    /// Decorate a program with inferred types.
    /// Returns a new program with type annotations added.
    pub fn decorate_program(&mut self, program: &Program, env: &TypeEnv) -> Program {
        let mut current_env = env.clone();
        let mut decorated_stmts = Vec::new();

        for stmt in &program.statements {
            let (decorated, new_env) = self.decorate_stmt(stmt, &current_env);
            decorated_stmts.push(decorated);
            current_env = new_env;
        }

        Program {
            statements: decorated_stmts,
            span: program.span,
        }
    }

    fn decorate_stmt(&mut self, stmt: &Stmt, env: &TypeEnv) -> (Stmt, TypeEnv) {
        match stmt {
            Stmt::Var {
                kind,
                declarations,
                span,
            } => {
                let mut new_env = env.clone();
                let decorated_decls: Vec<VarDeclarator> = declarations
                    .iter()
                    .map(|decl| {
                        let annotation = if decl.type_annotation.is_some() {
                            // Keep existing annotation
                            decl.type_annotation.clone()
                        } else if let Some(ty) = self.state.get_decl_type(decl.span) {
                            // Add inferred type annotation from decl_types map
                            Some(self.type_to_annotation(ty, decl.span))
                        } else if let Some(scheme) = env.lookup(&decl.name) {
                            // Fallback to env lookup for top-level declarations
                            Some(self.scheme_to_annotation(scheme, decl.span))
                        } else {
                            None
                        };

                        // Update env for subsequent declarations
                        if decl.init.is_some() {
                            // The type should already be in env from inference
                            if let Some(scheme) = env.lookup(&decl.name) {
                                new_env = new_env.extend(decl.name.clone(), scheme.clone());
                            }
                        }

                        VarDeclarator {
                            name: decl.name.clone(),
                            init: decl.init.as_ref().map(|e| self.decorate_expr(e, env)),
                            type_annotation: annotation,
                            kind: decl.kind,
                            span: decl.span,
                        }
                    })
                    .collect();

                (
                    Stmt::Var {
                        kind: *kind,
                        declarations: decorated_decls,
                        span: *span,
                    },
                    new_env,
                )
            }

            Stmt::FunctionDecl {
                name,
                params,
                body,
                type_annotation,
                span,
            } => {
                // For function declarations, always use the scheme from the environment
                // to get the generalized type with predicates
                let annotation = if type_annotation.is_some() {
                    type_annotation.clone()
                } else if let Some(scheme) = env.lookup(name) {
                    Some(self.scheme_to_annotation(scheme, *span))
                } else {
                    None
                };

                let (decorated_body, _) = self.decorate_stmt(body, env);

                let new_env = if let Some(scheme) = env.lookup(name) {
                    env.extend(name.clone(), scheme.clone())
                } else {
                    env.clone()
                };

                (
                    Stmt::FunctionDecl {
                        name: name.clone(),
                        params: params.clone(),
                        body: Box::new(decorated_body),
                        type_annotation: annotation,
                        span: *span,
                    },
                    new_env,
                )
            }

            Stmt::Block { body, span } => {
                let mut current_env = env.clone();
                let decorated_body: Vec<Stmt> = body
                    .iter()
                    .map(|s| {
                        let (decorated, new_env) = self.decorate_stmt(s, &current_env);
                        current_env = new_env;
                        decorated
                    })
                    .collect();

                (
                    Stmt::Block {
                        body: decorated_body,
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::If {
                test,
                consequent,
                alternate,
                span,
            } => {
                let decorated_test = self.decorate_expr(test, env);
                let (decorated_cons, _) = self.decorate_stmt(consequent, env);
                let decorated_alt = alternate
                    .as_ref()
                    .map(|a| Box::new(self.decorate_stmt(a, env).0));

                (
                    Stmt::If {
                        test: decorated_test,
                        consequent: Box::new(decorated_cons),
                        alternate: decorated_alt,
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::While { test, body, span } => {
                let decorated_test = self.decorate_expr(test, env);
                let (decorated_body, _) = self.decorate_stmt(body, env);

                (
                    Stmt::While {
                        test: decorated_test,
                        body: Box::new(decorated_body),
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::DoWhile { body, test, span } => {
                let (decorated_body, _) = self.decorate_stmt(body, env);
                let decorated_test = self.decorate_expr(test, env);

                (
                    Stmt::DoWhile {
                        body: Box::new(decorated_body),
                        test: decorated_test,
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::For {
                init,
                test,
                update,
                body,
                span,
            } => {
                let decorated_init = init.as_ref().map(|i| match i {
                    ForInit::VarDecl(decls) => ForInit::VarDecl(
                        decls
                            .iter()
                            .map(|d| {
                                let annotation = if d.type_annotation.is_some() {
                                    d.type_annotation.clone()
                                } else if let Some(ty) = self.state.get_decl_type(d.span) {
                                    Some(self.type_to_annotation(ty, d.span))
                                } else {
                                    None
                                };
                                VarDeclarator {
                                    name: d.name.clone(),
                                    init: d.init.as_ref().map(|e| self.decorate_expr(e, env)),
                                    type_annotation: annotation,
                                    kind: d.kind,
                                    span: d.span,
                                }
                            })
                            .collect(),
                    ),
                    ForInit::Expr(e) => ForInit::Expr(self.decorate_expr(e, env)),
                });
                let decorated_test = test.as_ref().map(|t| self.decorate_expr(t, env));
                let decorated_update = update.as_ref().map(|u| self.decorate_expr(u, env));
                let (decorated_body, _) = self.decorate_stmt(body, env);

                (
                    Stmt::For {
                        init: decorated_init,
                        test: decorated_test,
                        update: decorated_update,
                        body: Box::new(decorated_body),
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::ForIn {
                left,
                right,
                body,
                span,
            } => {
                let decorated_right = self.decorate_expr(right, env);
                let (decorated_body, _) = self.decorate_stmt(body, env);

                let decorated_left = match left {
                    ForInLhs::VarDecl(name, existing_ann, decl_span) => {
                        let annotation = if existing_ann.is_some() {
                            existing_ann.clone()
                        } else if let Some(ty) = self.state.get_decl_type(*decl_span) {
                            Some(self.type_to_annotation(ty, *decl_span))
                        } else {
                            None
                        };
                        ForInLhs::VarDecl(name.clone(), annotation, *decl_span)
                    }
                    ForInLhs::Expr(e) => ForInLhs::Expr(self.decorate_expr(e, env)),
                };

                (
                    Stmt::ForIn {
                        left: decorated_left,
                        right: decorated_right,
                        body: Box::new(decorated_body),
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::ForOf {
                left,
                right,
                body,
                span,
            } => {
                let decorated_right = self.decorate_expr(right, env);
                let (decorated_body, _) = self.decorate_stmt(body, env);

                let decorated_left = match left {
                    ForInLhs::VarDecl(name, existing_ann, decl_span) => {
                        let annotation = if existing_ann.is_some() {
                            existing_ann.clone()
                        } else if let Some(ty) = self.state.get_decl_type(*decl_span) {
                            Some(self.type_to_annotation(ty, *decl_span))
                        } else {
                            None
                        };
                        ForInLhs::VarDecl(name.clone(), annotation, *decl_span)
                    }
                    ForInLhs::Expr(e) => ForInLhs::Expr(self.decorate_expr(e, env)),
                };

                (
                    Stmt::ForOf {
                        left: decorated_left,
                        right: decorated_right,
                        body: Box::new(decorated_body),
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::Return { argument, span } => (
                Stmt::Return {
                    argument: argument.as_ref().map(|a| self.decorate_expr(a, env)),
                    span: *span,
                },
                env.clone(),
            ),

            Stmt::Throw { argument, span } => (
                Stmt::Throw {
                    argument: self.decorate_expr(argument, env),
                    span: *span,
                },
                env.clone(),
            ),

            Stmt::Try {
                block,
                handler,
                finalizer,
                span,
            } => {
                let (decorated_block, _) = self.decorate_stmt(block, env);
                let decorated_handler = handler.as_ref().map(|h| CatchClause {
                    param: h.param.clone(),
                    body: Box::new(self.decorate_stmt(&h.body, env).0),
                    span: h.span,
                });
                let decorated_finalizer = finalizer
                    .as_ref()
                    .map(|f| Box::new(self.decorate_stmt(f, env).0));

                (
                    Stmt::Try {
                        block: Box::new(decorated_block),
                        handler: decorated_handler,
                        finalizer: decorated_finalizer,
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::Switch {
                discriminant,
                cases,
                span,
            } => {
                let decorated_discrim = self.decorate_expr(discriminant, env);
                let decorated_cases: Vec<SwitchCase> = cases
                    .iter()
                    .map(|c| {
                        let decorated_test = c.test.as_ref().map(|t| self.decorate_expr(t, env));
                        let decorated_consequent: Vec<Stmt> = c
                            .consequent
                            .iter()
                            .map(|s| self.decorate_stmt(s, env).0)
                            .collect();

                        SwitchCase {
                            test: decorated_test,
                            consequent: decorated_consequent,
                            span: c.span,
                        }
                    })
                    .collect();

                (
                    Stmt::Switch {
                        discriminant: decorated_discrim,
                        cases: decorated_cases,
                        span: *span,
                    },
                    env.clone(),
                )
            }

            Stmt::Labeled { label, body, span } => {
                let (decorated_body, _) = self.decorate_stmt(body, env);
                (
                    Stmt::Labeled {
                        label: label.clone(),
                        body: Box::new(decorated_body),
                        span: *span,
                    },
                    env.clone(),
                )
            }

            // Import/Export statements pass through unchanged
            Stmt::Import {
                specifiers,
                source,
                span,
            } => (
                Stmt::Import {
                    specifiers: specifiers.clone(),
                    source: source.clone(),
                    span: *span,
                },
                env.clone(),
            ),
            Stmt::Export { declaration, span } => (
                Stmt::Export {
                    declaration: declaration.clone(),
                    span: *span,
                },
                env.clone(),
            ),

            // Statements that don't need decoration
            Stmt::Empty { span } => (Stmt::Empty { span: *span }, env.clone()),
            Stmt::Break { label, span } => (
                Stmt::Break {
                    label: label.clone(),
                    span: *span,
                },
                env.clone(),
            ),
            Stmt::Continue { label, span } => (
                Stmt::Continue {
                    label: label.clone(),
                    span: *span,
                },
                env.clone(),
            ),
            Stmt::Expr { expression, span } => (
                Stmt::Expr {
                    expression: self.decorate_expr(expression, env),
                    span: *span,
                },
                env.clone(),
            ),
        }
    }

    fn decorate_expr(&mut self, expr: &Expr, env: &TypeEnv) -> Expr {
        match expr {
            Expr::Function {
                name,
                params,
                body,
                type_annotation,
                span,
            } => {
                // For function expressions, we could add type annotations
                // but we'd need to track expression types, not just env bindings
                let (decorated_body, _) = self.decorate_stmt(body, env);
                Expr::Function {
                    name: name.clone(),
                    params: params.clone(),
                    body: Box::new(decorated_body),
                    type_annotation: type_annotation.clone(),
                    span: *span,
                }
            }

            Expr::Array { elements, span } => Expr::Array {
                elements: elements
                    .iter()
                    .map(|e| e.as_ref().map(|e| self.decorate_expr(e, env)))
                    .collect(),
                span: *span,
            },

            Expr::Object { properties, span } => Expr::Object {
                properties: properties
                    .iter()
                    .map(|p| self.decorate_prop(p, env))
                    .collect(),
                span: *span,
            },

            Expr::Call {
                callee,
                arguments,
                span,
            } => Expr::Call {
                callee: Box::new(self.decorate_expr(callee, env)),
                arguments: arguments
                    .iter()
                    .map(|a| self.decorate_expr(a, env))
                    .collect(),
                span: *span,
            },

            Expr::New {
                callee,
                arguments,
                span,
            } => Expr::New {
                callee: Box::new(self.decorate_expr(callee, env)),
                arguments: arguments
                    .iter()
                    .map(|a| self.decorate_expr(a, env))
                    .collect(),
                span: *span,
            },

            Expr::Member {
                object,
                property,
                span,
            } => Expr::Member {
                object: Box::new(self.decorate_expr(object, env)),
                property: property.clone(),
                span: *span,
            },

            Expr::ComputedMember {
                object,
                property,
                span,
            } => Expr::ComputedMember {
                object: Box::new(self.decorate_expr(object, env)),
                property: Box::new(self.decorate_expr(property, env)),
                span: *span,
            },

            Expr::Unary { op, argument, span } => Expr::Unary {
                op: *op,
                argument: Box::new(self.decorate_expr(argument, env)),
                span: *span,
            },

            Expr::Binary {
                op,
                left,
                right,
                span,
            } => Expr::Binary {
                op: *op,
                left: Box::new(self.decorate_expr(left, env)),
                right: Box::new(self.decorate_expr(right, env)),
                span: *span,
            },

            Expr::Assign {
                op,
                left,
                right,
                span,
            } => Expr::Assign {
                op: *op,
                left: Box::new(self.decorate_expr(left, env)),
                right: Box::new(self.decorate_expr(right, env)),
                span: *span,
            },

            Expr::Conditional {
                test,
                consequent,
                alternate,
                span,
            } => Expr::Conditional {
                test: Box::new(self.decorate_expr(test, env)),
                consequent: Box::new(self.decorate_expr(consequent, env)),
                alternate: Box::new(self.decorate_expr(alternate, env)),
                span: *span,
            },

            Expr::Sequence { expressions, span } => Expr::Sequence {
                expressions: expressions
                    .iter()
                    .map(|e| self.decorate_expr(e, env))
                    .collect(),
                span: *span,
            },

            Expr::TemplateLiteral {
                quasis,
                expressions,
                span,
            } => Expr::TemplateLiteral {
                quasis: quasis.clone(),
                expressions: expressions
                    .iter()
                    .map(|e| self.decorate_expr(e, env))
                    .collect(),
                span: *span,
            },

            // Expressions that don't need decoration
            other => other.clone(),
        }
    }

    fn decorate_prop(&mut self, prop: &PropDef, env: &TypeEnv) -> PropDef {
        match prop {
            PropDef::Property {
                key,
                value,
                type_annotation,
                span,
            } => PropDef::Property {
                key: key.clone(),
                value: self.decorate_expr(value, env),
                type_annotation: type_annotation.clone(),
                span: *span,
            },
            PropDef::Getter { key, body, span } => PropDef::Getter {
                key: key.clone(),
                body: Box::new(self.decorate_stmt(body, env).0),
                span: *span,
            },
            PropDef::Setter {
                key,
                param,
                body,
                span,
            } => PropDef::Setter {
                key: key.clone(),
                param: param.clone(),
                body: Box::new(self.decorate_stmt(body, env).0),
                span: *span,
            },
            PropDef::Method {
                key,
                params,
                body,
                span,
            } => PropDef::Method {
                key: key.clone(),
                params: params.clone(),
                body: Box::new(self.decorate_stmt(body, env).0),
                span: *span,
            },
        }
    }

    fn scheme_to_annotation(&mut self, scheme: &TypeScheme, span: Span) -> TypeAnnotation {
        // Apply substitution to the scheme's type and predicates
        let ty = self.state.apply_subst(&scheme.body.ty);
        let preds: Vec<_> = scheme
            .body
            .preds
            .iter()
            .map(|p| TypePred {
                class: p.class.clone(),
                types: p.types.iter().map(|t| self.state.apply_subst(t)).collect(),
            })
            .collect();

        // Only keep vars that are still free in the substituted type or predicates
        let ty_vars = ty.free_vars();
        let pred_vars: std::collections::HashSet<_> =
            preds.iter().flat_map(|p| p.free_vars()).collect();
        let used_vars: std::collections::HashSet<_> = ty_vars.union(&pred_vars).cloned().collect();

        // Collect all hidden this_type variables (from outer function and any function parameters)
        // These are hidden in display, so we shouldn't quantify over them
        let hidden_this_vars = collect_hidden_this_vars(&ty);

        let vars: Vec<_> = scheme
            .vars
            .iter()
            .filter(|v| used_vars.contains(v) && !hidden_this_vars.contains(v))
            .cloned()
            .collect();

        let applied_scheme = TypeScheme {
            vars,
            body: QualType::with_preds(preds, ty),
        };
        let content = self.ctx.format_scheme(&applied_scheme);
        TypeAnnotation {
            name: "".to_string(),
            content,
            span,
        }
    }

    fn type_to_annotation(&mut self, ty: &Type, span: Span) -> TypeAnnotation {
        let ty = self.state.apply_subst(ty);
        let content = self.ctx.format_type(&ty);
        TypeAnnotation {
            name: "".to_string(),
            content,
            span,
        }
    }
}

/// Convenience function to decorate a program with inferred types.
pub fn decorate_with_types(program: &Program, env: &TypeEnv, state: &InferState) -> Program {
    let mut decorator = Decorator::new(state);
    decorator.decorate_program(program, env)
}
