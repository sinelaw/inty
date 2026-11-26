//! AST decoration with inferred types.
//!
//! After type inference, this module walks the AST and adds type annotations
//! showing the inferred types for variables and functions.

use crate::ast::*;
use crate::span::Span;
use crate::types::{PrettyContext, Type, TypePred, TypeScheme};

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
                        } else if decl.init.is_none() {
                            // An annotated declaration without a value
                            // declares one defined elsewhere, a constant
                            // (`/** var x: T */ var x;`): an annotation
                            // would make `var x; x = 1;` an error.
                            None
                        } else if let Some(ty) = self.state.get_decl_type(decl.span) {
                            // Add inferred type annotation from decl_types map
                            self.type_to_annotation(ty, decl.span)
                        } else {
                            env.lookup(&decl.name)
                                .and_then(|scheme| self.scheme_to_annotation(scheme, decl.span))
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
                        .and_then(|scheme| self.scheme_to_annotation(scheme, *span))
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
                                } else if d.init.is_none() {
                                    None
                                } else {
                                    self.state
                                        .get_decl_type(d.span)
                                        .and_then(|ty| self.type_to_annotation(ty, d.span))
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
                                .and_then(|ty| self.type_to_annotation(ty, *decl_span))
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
                                .and_then(|ty| self.type_to_annotation(ty, *decl_span))
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

    /// The annotation `content`, when it reads back: it parses, and each
    /// name in it is a type in scope taking the arguments it is given
    /// (an instance's class by its name, `Menu<…>`). An annotation is
    /// optional, so a type that can't be written (one too large to show,
    /// or one only the checker can name) is left out rather than printed
    /// in a form the checker would reject.
    fn readable(
        &self,
        content: String,
        ty: &Type,
        preds: Option<&[TypePred]>,
        span: Span,
    ) -> Option<TypeAnnotation> {
        if !self.reads_back(&content, ty, preds) {
            return None;
        }
        Some(TypeAnnotation {
            name: "".to_string(),
            content,
            span,
            kind: crate::ast::AnnotationKind::Inline,
            content_start: None,
        })
    }

    /// Whether the annotation text `content`, written for `ty` (a
    /// displayed type, or a scheme's body), reads back as `ty`: it parses,
    /// each name in it is a type in scope taking the arguments it is
    /// given, and it parses to `ty`, up to the names of its variables.
    /// (Some types print in a form that parses to another: an open
    /// record's tail, `{x: T | a}`, reads as a field of type `T | a`, and a
    /// function's `this`, when it isn't known, isn't printed, so it reads
    /// as a function that uses none.)
    ///
    /// `preds` are the constraints of the scheme `ty` is the body of: a
    /// scheme's `this` that is a variable nothing else mentions (of a
    /// function that doesn't use `this`) is one it reads back as. A mere
    /// type's `this` variable may be constrained by what isn't shown.
    fn reads_back(&self, content: &str, ty: &Type, preds: Option<&[TypePred]>) -> bool {
        let Ok((parsed, _)) = crate::infer::type_parser::parse_type_annotation_with_aliases(
            content,
            Span::default(),
            0,
            &self.state.type_aliases,
        ) else {
            return false;
        };
        // A function annotation is of a function that uses no `this`,
        // unless it says.
        let canonical = |t: &Type| {
            let t = crate::infer::lower::annotation_this(&as_function(t), &Type::ArrowThis);
            crate::types::TidyEnv::new().tidy_type(&t)
        };
        let ty = match preds {
            Some(preds) => unused_this_dropped(ty, preds),
            None => ty.clone(),
        };
        canonical(&parsed) == canonical(&ty)
    }

    /// Types printed with each class's instance by the class's name.
    fn pretty(&self) -> PrettyContext {
        PrettyContext::with_nominal_names(self.state.nominal_names())
    }

    fn scheme_to_annotation(&mut self, scheme: &TypeScheme, span: Span) -> Option<TypeAnnotation> {
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
            return None;
        }
        let displayed = self.state.display_scheme(scheme);
        let content = self.pretty().format_scheme(&displayed);
        self.readable(
            content,
            &displayed.body.ty,
            Some(&displayed.body.preds),
            span,
        )
    }

    fn type_to_annotation(&mut self, ty: &Type, span: Span) -> Option<TypeAnnotation> {
        if self.state.flattened_size(ty) > MAX_SHOWN_TYPE {
            return None;
        }
        let displayed = self.state.display_type(ty);
        let content = self.pretty().format_type(&displayed);
        self.readable(content, &displayed, None, span)
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
                // The source's own line ending, as the line before ends.
                let newline = if source[..line_start].ends_with("\r\n") {
                    "\r\n"
                } else {
                    "\n"
                };
                text.insert_str(rel, &format!("/** {annotation} */{newline}{before}"));
            } else {
                text.insert_str(rel, &format!("/** {annotation} */ "));
            }
        }
        self.classes.insert(span, text);
    }

    /// `function NAME(…) => R` for the method `name` of the class whose
    /// constructor has `scheme`: the method's type in the class's instance,
    /// without its `this` (which an annotated method's is). `None` when
    /// the type isn't known, has type variables (a method's annotation
    /// can't: they would be the class's, the same at every call on an
    /// instance, not "for every type"), or doesn't read back.
    fn method_annotation(
        &self,
        scheme: &TypeScheme,
        name: &str,
        params: &[Param],
    ) -> Option<String> {
        let ctor = self.state.flatten_type(&scheme.body.ty);
        let (_, _, instance) = super::features::functions::extract_callable(&ctor)?;
        // The instance's members: the class's type's (or a row's that is
        // only it), or, for a class not typed nominally (`export default
        // class { … }`), the instance's own record's.
        let named = match &instance {
            Type::Named(id, args) => Some((id, args)),
            Type::Row(row) if row.props.is_empty() => match &row.tail {
                crate::types::RowTail::Recursive(id, args) => Some((id, args)),
                _ => return None,
            },
            Type::Row(_) => None,
            _ => return None,
        };
        let members = match named {
            Some((id, args)) => self.state.unroll_named(*id, args)?,
            None => instance,
        };
        let Type::Row(members) = members else {
            return None;
        };
        let entry = members
            .props
            .get(&crate::types::PropName::from(name.to_string()))?;
        let method = self.state.flatten_type(&entry.ty);
        let (_, method_params, ret) = super::features::functions::extract_callable(&method)?;
        let method_params = method_params
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
            this_type: None,
            params: method_params,
            ret: Box::new(ret),
        };
        if self.state.flattened_size(&ty) > MAX_SHOWN_TYPE || !ty.free_vars().is_empty() {
            return None;
        }
        let displayed = self.state.display_type(&ty);
        let content = self.pretty().showing_param_names().format_type(&displayed);
        if !self.reads_back(&content, &displayed, None) {
            return None;
        }
        Some(format!("function {name}{content}"))
    }
}

/// `ty` with each function's `this` left out where it is a variable
/// that occurs nowhere else in `ty` or `preds` (a function's that doesn't
/// use `this`, which an annotation doesn't write).
fn unused_this_dropped(ty: &Type, preds: &[TypePred]) -> Type {
    let mut counts: std::collections::HashMap<crate::types::TVarName, usize> =
        std::collections::HashMap::new();
    count_vars(ty, &mut counts);
    for p in preds {
        for t in &p.types {
            count_vars(t, &mut counts);
        }
    }
    drop_this(ty, &counts)
}

/// How many times each variable occurs in `ty`.
fn count_vars(ty: &Type, counts: &mut std::collections::HashMap<crate::types::TVarName, usize>) {
    match ty {
        Type::Var(v) => *counts.entry(v.clone()).or_default() += 1,
        Type::Func {
            this_type,
            params,
            ret,
        } => {
            if let Some(t) = this_type {
                count_vars(t, counts);
            }
            for p in params {
                count_vars(&p.ty, counts);
            }
            count_vars(ret, counts);
        }
        Type::Row(row) => {
            for e in row.props.values() {
                count_vars(&e.ty, counts);
            }
            match &row.tail {
                crate::types::RowTail::Open(v) => *counts.entry(v.clone()).or_default() += 1,
                crate::types::RowTail::Recursive(_, args) => {
                    args.iter().for_each(|a| count_vars(a, counts))
                }
                crate::types::RowTail::Closed => {}
            }
        }
        Type::Array(t) | Type::Map(t) | Type::Promise(t) | Type::Maybe(_, t) => {
            count_vars(t, counts)
        }
        Type::Tuple(ts) | Type::Union(ts) | Type::Named(_, ts) => {
            ts.iter().for_each(|t| count_vars(t, counts))
        }
        _ => {}
    }
}

fn drop_this(ty: &Type, counts: &std::collections::HashMap<crate::types::TVarName, usize>) -> Type {
    let go = |t: &Type| drop_this(t, counts);
    match ty {
        Type::Func {
            this_type,
            params,
            ret,
        } => Type::Func {
            this_type: match this_type.as_deref() {
                Some(Type::Var(v)) if counts.get(v) == Some(&1) => None,
                other => other.map(|t| Box::new(go(t))),
            },
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
            for e in row.props.values_mut() {
                e.ty = go(&e.ty);
            }
            Type::Row(row)
        }
        Type::Array(t) => Type::Array(Box::new(go(t))),
        Type::Map(t) => Type::Map(Box::new(go(t))),
        Type::Promise(t) => Type::Promise(Box::new(go(t))),
        Type::Maybe(n, t) => Type::Maybe(*n, Box::new(go(t))),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(go).collect()),
        Type::Union(ts) => Type::Union(ts.iter().map(go).collect()),
        Type::Named(id, ts) => Type::Named(*id, ts.iter().map(go).collect()),
        other => other.clone(),
    }
}

/// A callable record of only a call signature, as its function type.
fn as_function(ty: &Type) -> Type {
    if let Type::Row(row) = ty {
        let key = crate::types::PropName(crate::types::CALLABLE_KEY.to_string());
        if let (Some(entry), 1, crate::types::RowTail::Closed) =
            (row.props.get(&key), row.props.len(), &row.tail)
        {
            return entry.ty.clone();
        }
    }
    ty.clone()
}

/// The methods (on the prototype, not private, without an annotation of
/// their own) of
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
            } if crate::types::private_key_display(&crate::types::PropName(name.clone()))
                .is_none() =>
            {
                // (A private method, `#m() {}`, takes no annotation.)
                Some((name.as_str(), params.as_slice(), span.start))
            }
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
