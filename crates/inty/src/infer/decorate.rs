//! AST decoration with inferred types.
//!
//! After type inference, this module walks the AST and adds type annotations
//! showing the inferred types for variables and functions.

use crate::ast::*;
use crate::span::Span;
use crate::types::{PrettyContext, Type, TypeScheme};

use super::env::TypeEnv;
use super::state::InferState;

/// Decorate an AST with inferred type annotations.
///
/// Holds no mutable display state: each annotation goes through
/// [`InferState::display_type`] / [`InferState::display_scheme`],
/// which produce already-tidied values that print the same with a
/// fresh [`PrettyContext`].
pub struct Decorator<'a> {
    state: &'a InferState,
    /// The program's source, when its classes are to be shown as written
    /// (see [`decorate_with_classes`]).
    source: Option<&'a str>,
    /// Each class's text, keyed by its declaration's span: its source with
    /// an annotation above each method.
    classes: std::collections::HashMap<Span, String>,
    /// The spans of the program's class declarations.
    class_decls: std::collections::HashSet<Span>,
}

impl<'a> Decorator<'a> {
    pub fn new(state: &'a InferState) -> Self {
        Self {
            state,
            source: None,
            classes: std::collections::HashMap::new(),
            class_decls: std::collections::HashSet::new(),
        }
    }

    /// Decorate a program with inferred types.
    /// Returns a new program with type annotations added.
    pub fn decorate_program(&mut self, program: &Program, env: &TypeEnv) -> Program {
        self.class_decls = program.class_decls.iter().copied().collect();
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
            type_aliases: program.type_aliases.clone(),
            class_brands: program.class_brands.clone(),
            class_decls: program.class_decls.clone(),
            language: program.language,
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
                        } else {
                            env.lookup(&decl.name)
                                .map(|scheme| self.scheme_to_annotation(scheme, decl.span))
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
                            type_ast: None,
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
                return_type_ast,
                name_span,
                span,
            } => {
                // For function declarations, always use the scheme from the environment
                // to get the generalized type with predicates
                let annotation = if type_annotation.is_some() {
                    type_annotation.clone()
                } else {
                    env.lookup(name)
                        .map(|scheme| self.scheme_to_annotation(scheme, *span))
                };

                self.note_class(name, body, *span, *name_span, env);
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
                        return_type_ast: return_type_ast.clone(),
                        name_span: *name_span,
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
                                } else {
                                    self.state
                                        .get_decl_type(d.span)
                                        .map(|ty| self.type_to_annotation(ty, d.span))
                                };
                                VarDeclarator {
                                    name: d.name.clone(),
                                    init: d.init.as_ref().map(|e| self.decorate_expr(e, env)),
                                    type_annotation: annotation,
                                    type_ast: None,
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
                    ForInLhs::VarDecl(name, existing_ann, decl_span, kind) => {
                        let annotation = if existing_ann.is_some() {
                            existing_ann.clone()
                        } else {
                            self.state
                                .get_decl_type(*decl_span)
                                .map(|ty| self.type_to_annotation(ty, *decl_span))
                        };
                        ForInLhs::VarDecl(name.clone(), annotation, *decl_span, *kind)
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
                    ForInLhs::VarDecl(name, existing_ann, decl_span, kind) => {
                        let annotation = if existing_ann.is_some() {
                            existing_ann.clone()
                        } else {
                            self.state
                                .get_decl_type(*decl_span)
                                .map(|ty| self.type_to_annotation(ty, *decl_span))
                        };
                        ForInLhs::VarDecl(name.clone(), annotation, *decl_span, *kind)
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
                {
                    match declaration {
                        ExportDecl::Function {
                            name,
                            body,
                            span: decl_span,
                            ..
                        } => self.note_class(name, body, *decl_span, None, env),
                        ExportDecl::Default {
                            value:
                                Expr::Function {
                                    name: Some(name),
                                    body,
                                    span: decl_span,
                                    ..
                                },
                            ..
                        } => self.note_class(name, body, *decl_span, None, env),
                        _ => {}
                    }
                    Stmt::Export {
                        declaration: declaration.clone(),
                        span: *span,
                    }
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
                arrow,
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
                    arrow: *arrow,
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
                keywords,
                span,
            } => Expr::Call {
                callee: Box::new(self.decorate_expr(callee, env)),
                arguments: arguments
                    .iter()
                    .map(|a| self.decorate_expr(a, env))
                    .collect(),
                keywords: keywords
                    .iter()
                    .map(|(n, e)| (n.clone(), self.decorate_expr(e, env)))
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
                type_ast,
                span,
            } => PropDef::Property {
                key: key.clone(),
                value: self.decorate_expr(value, env),
                type_annotation: type_annotation.clone(),
                type_ast: type_ast.clone(),
                span: *span,
            },
            PropDef::Getter {
                key,
                body,
                proto,
                span,
            } => PropDef::Getter {
                key: key.clone(),
                body: Box::new(self.decorate_stmt(body, env).0),
                proto: *proto,
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
                return_type_ast,
                type_annotation,
                proto,
                span,
            } => PropDef::Method {
                key: key.clone(),
                params: params.clone(),
                body: Box::new(self.decorate_stmt(body, env).0),
                return_type_ast: return_type_ast.clone(),
                type_annotation: type_annotation.clone(),
                proto: *proto,
                span: *span,
            },
            PropDef::Spread { argument, span } => PropDef::Spread {
                argument: self.decorate_expr(argument, env),
                span: *span,
            },
        }
    }

    fn scheme_to_annotation(&mut self, scheme: &TypeScheme, span: Span) -> TypeAnnotation {
        // `display_scheme` flattens *and* tidies, so the resulting
        // scheme carries canonical, traversal-ordered IDs. A fresh
        // `PrettyContext` per annotation now produces the same
        // letters another caller would for the same scheme — the
        // mutable letter map is no longer load-bearing.
        let size = std::iter::once(&scheme.body.ty)
            .chain(scheme.body.preds.iter().flat_map(|p| p.types.iter()))
            .map(|t| self.state.flattened_size(t))
            .fold(0usize, usize::saturating_add);
        if size > MAX_SHOWN_TYPE {
            return too_large(span);
        }
        let displayed = self.state.display_scheme(scheme);
        let mut ctx = PrettyContext::new();
        TypeAnnotation {
            name: "".to_string(),
            content: ctx.format_scheme(&displayed),
            span,
            kind: crate::ast::AnnotationKind::Inline,
            content_start: None,
        }
    }

    fn type_to_annotation(&mut self, ty: &Type, span: Span) -> TypeAnnotation {
        if self.state.flattened_size(ty) > MAX_SHOWN_TYPE {
            return too_large(span);
        }
        let displayed = self.state.display_type(ty);
        let mut ctx = PrettyContext::new();
        TypeAnnotation {
            name: "".to_string(),
            content: ctx.format_type(&displayed),
            span,
            kind: crate::ast::AnnotationKind::Inline,
            content_start: None,
        }
    }
}

impl Decorator<'_> {
    /// When the function declared at `span` is a class's (lowered from
    /// `class NAME { … }`), its text as written, with an annotation above
    /// each method that has none (`/** function m(x: T) => R */`, which
    /// the checker reads back), kept for the printer.
    fn note_class(
        &mut self,
        name: &str,
        body: &Stmt,
        span: Span,
        name_span: Option<Span>,
        env: &TypeEnv,
    ) {
        let Some(source) = self.source else {
            return;
        };
        if !self.class_decls.contains(&span) || span.end > source.len() {
            return;
        }
        let scheme = self
            .state
            .get_decl_scheme(crate::ast::function_name_span(name_span, span, name))
            .or_else(|| env.lookup(name));
        let mut inserts: Vec<(usize, String)> = Vec::new();
        if let Some(scheme) = scheme {
            for (method, params, at) in class_methods(body) {
                if let Some(text) = self.method_annotation(scheme, method, params) {
                    inserts.push((at, text));
                }
            }
        }
        // Each annotation on a line of its own above its method, indented
        // as it is (or, after something else on the method's line, just
        // before it).
        let mut text = source[span.start..span.end].to_string();
        inserts.sort_by_key(|(at, _)| std::cmp::Reverse(*at));
        for (at, annotation) in inserts {
            if at < span.start || at > span.end {
                continue;
            }
            let line_start = source[..at].rfind('\n').map_or(0, |i| i + 1);
            let before = &source[line_start..at];
            let rel = at - span.start;
            if line_start >= span.start && before.chars().all(char::is_whitespace) {
                text.insert_str(rel, &format!("/** {annotation} */\n{before}"));
            } else {
                text.insert_str(rel, &format!("/** {annotation} */ "));
            }
        }
        self.classes.insert(span, text);
    }

    /// `function NAME(…) => R` for the method `name` of the class whose
    /// constructor has `scheme`: the method's type in the class's
    /// instance, with the class's type variables it mentions (and their
    /// constraints) quantified, and `this` left out when it is the
    /// instance (an annotated method's `this` is). `None` when the type
    /// isn't known or is too large to show.
    fn method_annotation(
        &self,
        scheme: &TypeScheme,
        name: &str,
        params: &[Param],
    ) -> Option<String> {
        let ctor = self.state.flatten_type(&scheme.body.ty);
        let (_, _, ret) = super::features::functions::extract_callable(&ctor)?;
        // The instance: the class's type, or a row that is only it.
        let (class_id, args) = match &ret {
            Type::Named(id, args) => (id, args),
            Type::Row(row) if row.props.is_empty() => match &row.tail {
                crate::types::RowTail::Recursive(id, args) => (id, args),
                _ => return None,
            },
            _ => return None,
        };
        let Type::Row(instance) = self.state.unroll_named(*class_id, args)? else {
            return None;
        };
        let entry = instance
            .props
            .get(&crate::types::PropName::from(name.to_string()))?;
        let method = self.state.flatten_type(&entry.ty);
        let (this_type, method_params, ret) =
            super::features::functions::extract_callable(&method)?;
        // The instance, as the class's type (`Counter`, printed by name):
        // the class's type itself, or a record of the instance's fields
        // (an argument of the class), which a method's `this` and a
        // `return this` are. As the language server shows a record of an
        // object's own fields as `Self`, it is told by its fields' names.
        let class = Type::Named(*class_id, args.clone());
        let fields: Option<Vec<&crate::types::PropName>> =
            match self.field_row_param(*class_id).and_then(|i| args.get(i)) {
                Some(Type::Row(r)) if !r.props.is_empty() => Some(r.props.keys().collect()),
                _ => None,
            };
        let is_instance = |t: &Type| match t {
            Type::Named(id, _) => id == class_id,
            Type::Row(r) if r.props.is_empty() => {
                matches!(&r.tail, crate::types::RowTail::Recursive(id, _) if id == class_id)
            }
            Type::Row(r) => fields.as_ref() == Some(&r.props.keys().collect()),
            _ => false,
        };
        let this_type = match &this_type {
            None | Some(Type::ArrowThis | Type::NewTarget | Type::Var(_)) => None,
            Some(t) if is_instance(t) => None,
            Some(t) => Some(Box::new(naming_instance(t, &is_instance, &class))),
        };
        // A method whose type mentions its own class (a `return this`)
        // has none written: the class's type takes its own field record as
        // an argument, which can't be written out.
        let mentions_class = |t: &Type| naming_instance(t, &is_instance, &Type::Error) != *t;
        if mentions_class(&ret) || method_params.iter().any(|p| mentions_class(&p.ty)) {
            return None;
        }
        let ret = Box::new(naming_instance(&ret, &is_instance, &class));
        let method_params = method_params
            .into_iter()
            .map(|mut p| {
                p.ty = naming_instance(&p.ty, &is_instance, &class);
                p
            })
            .collect::<Vec<_>>();
        let method_params: Vec<crate::types::FuncParam> = method_params
            .into_iter()
            .enumerate()
            .map(|(i, mut p)| {
                if p.name.is_none() {
                    p.name = params.get(i).map(|p| p.name.clone());
                }
                p
            })
            .collect();
        let ty = Type::Func {
            this_type,
            params: method_params,
            ret,
        };
        if self.state.flattened_size(&ty) > MAX_SHOWN_TYPE {
            return None;
        }
        // The class's variables the method mentions, and the constraints
        // on them (with the variables those mention).
        let mut vars = ty.free_vars();
        let mut preds = Vec::new();
        let mut taken = vec![false; scheme.body.preds.len()];
        loop {
            let mut grew = false;
            for (i, p) in scheme.body.preds.iter().enumerate() {
                if taken[i] {
                    continue;
                }
                let pred_vars: std::collections::HashSet<_> = p
                    .types
                    .iter()
                    .flat_map(|t| self.state.flatten_type(t).free_vars())
                    .collect();
                if pred_vars.iter().any(|v| vars.contains(v)) {
                    taken[i] = true;
                    preds.push(p.clone());
                    vars.extend(pred_vars);
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        // Every variable, which an annotation declares: the class's, in
        // its order, then any other.
        let mut quantified: Vec<_> = scheme
            .vars
            .iter()
            .filter(|v| vars.contains(v))
            .cloned()
            .collect();
        let mut rest: Vec<_> = vars
            .into_iter()
            .filter(|v| !quantified.contains(v))
            .collect();
        rest.sort_by_key(|v| v.id());
        quantified.extend(rest);
        let method_scheme = TypeScheme {
            vars: quantified,
            pvars: scheme.pvars.clone(),
            body: crate::types::QualType::with_preds(preds, ty),
        };
        let displayed = self.state.display_scheme(&method_scheme);
        let mut ctx =
            PrettyContext::with_nominal_names(self.state.nominal_names()).showing_param_names();
        let content = ctx.format_scheme(&displayed);
        // Shown only if it reads back: each name a type in scope, with
        // its arguments.
        crate::infer::type_parser::parse_type_annotation_with_aliases(
            &content,
            Span::default(),
            0,
            &self.state.type_aliases,
        )
        .ok()?;
        let gap = if content.starts_with(['(', '<']) {
            ""
        } else {
            " "
        };
        Some(format!("function {name}{gap}{content}"))
    }
}

impl Decorator<'_> {
    /// Which of the class `class_id`'s parameters is its instance's field
    /// row: the one its methods take `this` as (`{ | ρ}`).
    fn field_row_param(&self, class_id: crate::types::TypeId) -> Option<usize> {
        let def = self.state.get_named_type(class_id)?;
        let Type::Row(body) = &def.body else {
            return None;
        };
        body.props.values().find_map(|entry| {
            let (this, _, _) = super::features::functions::extract_callable(&entry.ty)?;
            match this? {
                Type::Row(r) if r.props.is_empty() => match &r.tail {
                    crate::types::RowTail::Open(v) => def.params.iter().position(|p| p == v),
                    _ => None,
                },
                _ => None,
            }
        })
    }
}

/// `ty` with each type `is_instance` holds of replaced by `class`.
fn naming_instance(ty: &Type, is_instance: &dyn Fn(&Type) -> bool, class: &Type) -> Type {
    if is_instance(ty) {
        return class.clone();
    }
    let go = |t: &Type| naming_instance(t, is_instance, class);
    match ty {
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: this_type.as_ref().map(|t| Box::new(go(t))),
            params: params
                .iter()
                .map(|p| {
                    let mut p = p.clone();
                    p.ty = go(&p.ty);
                    p
                })
                .collect(),
            ret: Box::new(go(ret)),
        },
        Type::Row(row) => {
            let mut row = row.clone();
            for entry in row.props.values_mut() {
                entry.ty = go(&entry.ty);
            }
            Type::Row(row)
        }
        Type::Array(t) => Type::Array(Box::new(go(t))),
        Type::Map(t) => Type::Map(Box::new(go(t))),
        Type::Promise(t) => Type::Promise(Box::new(go(t))),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(go).collect()),
        Type::Union(ts) => Type::Union(ts.iter().map(go).collect()),
        Type::Named(id, args) => Type::Named(*id, args.iter().map(go).collect()),
        Type::Maybe(n, t) => Type::Maybe(*n, Box::new(go(t))),
        other => other.clone(),
    }
}

/// The methods (on the prototype, without an annotation of their own) of
/// the class lowered to a function whose body is `body`: each one's name,
/// parameters and where it starts.
fn class_methods(body: &Stmt) -> Vec<(&str, &[Param], usize)> {
    let Stmt::Block { body, .. } = body else {
        return Vec::new();
    };
    let Some(Stmt::Return {
        argument: Some(Expr::Object { properties, .. }),
        ..
    }) = body.last()
    else {
        return Vec::new();
    };
    properties
        .iter()
        .filter_map(|p| match p {
            PropDef::Method {
                key: PropKey::Ident(name),
                params,
                type_annotation: None,
                proto: true,
                span,
                ..
            } => Some((name.as_str(), params.as_slice(), span.start)),
            _ => None,
        })
        .collect()
}

/// Decorate a program with inferred types, and give each of its classes'
/// text as written in `source`, with an annotation above each method,
/// keyed by the class's span (for [`crate::ast::pretty::print_program_with`]).
pub fn decorate_with_classes(
    program: &Program,
    env: &TypeEnv,
    state: &InferState,
    source: &str,
) -> (Program, std::collections::HashMap<Span, String>) {
    let mut decorator = Decorator::new(state);
    decorator.source = Some(source);
    let decorated = decorator.decorate_program(program, env);
    (decorated, decorator.classes)
}

/// Convenience function to decorate a program with inferred types.
pub fn decorate_with_types(program: &Program, env: &TypeEnv, state: &InferState) -> Program {
    let mut decorator = Decorator::new(state);
    decorator.decorate_program(program, env)
}

/// The largest type (in nodes, written out) an annotation shows. A type
/// that mentions a large one in many places (a DOM element's row, in each
/// of its event handlers' events) written out whole would be unreadable
/// and could take more memory than there is.
const MAX_SHOWN_TYPE: usize = 20_000;

/// The annotation of a declaration whose type is too large to show.
fn too_large(span: Span) -> TypeAnnotation {
    TypeAnnotation {
        name: "".to_string(),
        content: "… (a type too large to show)".to_string(),
        span,
        kind: crate::ast::AnnotationKind::Inline,
        content_start: None,
    }
}
