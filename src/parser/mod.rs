//! Parser module for mquickjs JavaScript source code.

pub mod ast;
pub mod pretty;

#[cfg(test)]
mod proptests;

use crate::error::{ParseError, Result};
use crate::lexer::{Span, Spanned, Token};
use ast::*;

/// Parser-internal destructuring pattern. Not part of the public AST —
/// every pattern is immediately lowered to ordinary declarators via
/// [`Parser::desugar_pattern`] before any other code sees it.
#[derive(Debug, Clone)]
enum Pattern {
    Ident(String, Span),
    /// `{source: sub_pattern, ...}`. Shorthand `{a}` stores
    /// `("a", Pattern::Ident("a"))`.
    Object(Vec<(String, Pattern, Span)>, Span),
    /// `[sub_pattern, sub_pattern, ...]`.
    Array(Vec<Pattern>, Span),
}

/// The parser for mquickjs source code.
pub struct Parser {
    tokens: Vec<Spanned<Token>>,
    pos: usize,
    /// Type annotations extracted by the lexer
    type_annotations: Vec<TypeAnnotation>,
    annotation_pos: usize,
    /// Whether to disallow 'in' as a binary operator (for for-loop init)
    no_in: bool,
    /// Counter for synthesised temp names (used when desugaring
    /// destructuring patterns into a sequence of simple declarators).
    temp_counter: usize,
    /// How many enclosing `async` functions we're currently inside of.
    /// `await` is legal only when this is > 0.
    async_depth: usize,
    /// Set by the `async function` parser arm before it hands off to the
    /// generic function-declaration / function-expression parser; read
    /// (and immediately cleared) by that parser to decide whether the
    /// body it's about to read should start in an async context.
    next_fn_is_async: bool,
}

impl Parser {
    pub fn new(tokens: Vec<Spanned<Token>>, type_annotations: Vec<TypeAnnotation>) -> Self {
        Self {
            tokens,
            pos: 0,
            type_annotations,
            annotation_pos: 0,
            no_in: false,
            temp_counter: 0,
            async_depth: 0,
            next_fn_is_async: false,
        }
    }

    fn fresh_temp_name(&mut self) -> String {
        let n = self.temp_counter;
        self.temp_counter += 1;
        format!("$destr${}", n)
    }

    /// Parse an expression with 'in' disallowed as a binary operator
    fn parse_expression_no_in(&mut self) -> Result<Expr> {
        let old = self.no_in;
        self.no_in = true;
        let result = self.parse_expression();
        self.no_in = old;
        result
    }

    /// Parse the entire program
    pub fn parse_program(&mut self) -> Result<Program> {
        let start = self.current_span().start;
        let mut statements = Vec::new();

        while !self.is_at_end() {
            statements.push(self.parse_statement()?);
        }

        let end = if statements.is_empty() {
            start
        } else {
            statements.last().unwrap().span().end
        };

        Ok(Program {
            statements,
            span: Span::new(start, end),
        })
    }

    // ========== Statement Parsing ==========

    fn parse_statement(&mut self) -> Result<Stmt> {
        match self.current() {
            Token::Var => self.parse_var_declaration(VarKind::Var),
            // `let` is parsed as `var`. minfern doesn't yet model per-block
            // lexical scoping or temporal-dead-zone rules, but var-with-block
            // scoping is a sound over-approximation for type checking.
            Token::Let => self.parse_var_declaration(VarKind::Var),
            Token::Const => self.parse_var_declaration(VarKind::Const),
            Token::Function => self.parse_function_declaration(),
            Token::Class => self.parse_class_declaration(),
            // `async function name(...) { body }` parses like a regular
            // function declaration; `async` is consumed by the async-wrap
            // helper which rewrites every `return` inside the body so the
            // function's return type ends up as `Promise<T>`.
            Token::Async if matches!(self.tokens.get(self.pos + 1).map(|s| &s.value), Some(Token::Function)) => {
                self.advance(); // consume `async`
                // Signal to the upcoming function parse that its body
                // should start in an async context. The flag is a
                // one-shot: the function parser reads and clears it
                // before descending into the body.
                self.next_fn_is_async = true;
                let decl_result = self.parse_function_declaration();
                Ok(Self::make_async_function_decl(decl_result?))
            }
            Token::Import => self.parse_import_declaration(),
            Token::Export => self.parse_export_declaration(),
            Token::If => self.parse_if_statement(),
            Token::While => self.parse_while_statement(),
            Token::Do => self.parse_do_while_statement(),
            Token::For => self.parse_for_statement(),
            Token::Return => self.parse_return_statement(),
            Token::Throw => self.parse_throw_statement(),
            Token::Try => self.parse_try_statement(),
            Token::Switch => self.parse_switch_statement(),
            Token::Break => self.parse_break_statement(),
            Token::Continue => self.parse_continue_statement(),
            Token::LBrace => self.parse_block_statement(),
            Token::Semicolon => {
                let span = self.current_span();
                self.advance();
                Ok(Stmt::Empty { span })
            }
            Token::Ident(_) => {
                // Could be labeled statement or expression statement
                if self.peek_is(&Token::Colon) {
                    self.parse_labeled_statement()
                } else {
                    self.parse_expression_statement()
                }
            }
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_block_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::LBrace)?;

        let mut body = Vec::new();
        while !self.check(&Token::RBrace) && !self.is_at_end() {
            body.push(self.parse_statement()?);
        }

        let end_span = self.current_span();
        self.expect(&Token::RBrace)?;

        Ok(Stmt::Block {
            body,
            span: Span::new(start, end_span.end),
        })
    }

    fn parse_var_declaration(&mut self, kind: VarKind) -> Result<Stmt> {
        let start = self.current_span().start;
        // Consume either 'var' or 'const'
        self.advance();

        let mut declarations = Vec::new();

        loop {
            // A destructuring pattern at the start of a declarator desugars
            // into a small sequence of ordinary declarators sharing a
            // synthesised temp binding. Patterns may nest.
            if self.check(&Token::LBrace) || self.check(&Token::LBracket) {
                declarations.extend(self.parse_destructuring_decl(kind)?);
            } else {
                declarations.push(self.parse_var_declarator(kind)?);
            }

            if !self.consume_if(&Token::Comma) {
                break;
            }
        }

        self.consume_semicolon();

        let end = declarations.last().map(|d| d.span.end).unwrap_or(start);

        Ok(Stmt::Var {
            kind,
            declarations,
            span: Span::new(start, end),
        })
    }

    /// Parse a destructuring pattern (may be nested: `{a: {b: [c, d]}}`).
    /// Doesn't emit declarators — caller passes the result to
    /// [`Self::desugar_pattern`] along with a source expression.
    fn parse_pattern(&mut self) -> Result<Pattern> {
        if self.check(&Token::LBrace) {
            self.parse_object_pattern()
        } else if self.check(&Token::LBracket) {
            self.parse_array_pattern()
        } else {
            let span = self.current_span();
            let name = self.expect_ident()?;
            Ok(Pattern::Ident(name, span))
        }
    }

    fn parse_object_pattern(&mut self) -> Result<Pattern> {
        let start = self.current_span().start;
        self.expect(&Token::LBrace)?;
        let mut entries: Vec<(String, Pattern, Span)> = Vec::new();
        while !self.check(&Token::RBrace) {
            let entry_span = self.current_span();
            let source = self.expect_ident()?;
            let sub = if self.consume_if(&Token::Colon) {
                self.parse_pattern()?
            } else {
                // Shorthand `{a}` is `{a: a}`.
                Pattern::Ident(source.clone(), entry_span)
            };
            entries.push((source, sub, entry_span));
            if !self.consume_if(&Token::Comma) {
                break;
            }
        }
        self.expect(&Token::RBrace)?;
        let end = self.prev_span().end;
        Ok(Pattern::Object(entries, Span::new(start, end)))
    }

    fn parse_array_pattern(&mut self) -> Result<Pattern> {
        let start = self.current_span().start;
        self.expect(&Token::LBracket)?;
        let mut elems: Vec<Pattern> = Vec::new();
        while !self.check(&Token::RBracket) {
            elems.push(self.parse_pattern()?);
            if !self.consume_if(&Token::Comma) {
                break;
            }
        }
        self.expect(&Token::RBracket)?;
        let end = self.prev_span().end;
        Ok(Pattern::Array(elems, Span::new(start, end)))
    }

    /// Produce a flat list of declarators that destructure `source` into
    /// the bindings named by `pattern`. Object / array patterns recurse
    /// through a fresh temp binding so arbitrarily nested patterns work.
    fn desugar_pattern(
        &mut self,
        pattern: &Pattern,
        source: Expr,
        kind: VarKind,
        decls: &mut Vec<VarDeclarator>,
    ) {
        match pattern {
            Pattern::Ident(name, span) => {
                decls.push(VarDeclarator {
                    name: name.clone(),
                    init: Some(source),
                    type_annotation: None,
                    kind,
                    span: *span,
                });
            }
            Pattern::Object(entries, span) => {
                let temp = self.fresh_temp_name();
                decls.push(VarDeclarator {
                    name: temp.clone(),
                    init: Some(source),
                    type_annotation: None,
                    kind,
                    span: *span,
                });
                for (prop_name, sub, prop_span) in entries {
                    let access = Expr::Member {
                        object: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *prop_span,
                        }),
                        property: prop_name.clone(),
                        span: *prop_span,
                    };
                    self.desugar_pattern(sub, access, kind, decls);
                }
            }
            Pattern::Array(elems, span) => {
                let temp = self.fresh_temp_name();
                decls.push(VarDeclarator {
                    name: temp.clone(),
                    init: Some(source),
                    type_annotation: None,
                    kind,
                    span: *span,
                });
                for (idx, sub) in elems.iter().enumerate() {
                    let elem_span = *span;
                    let access = Expr::ComputedMember {
                        object: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: elem_span,
                        }),
                        property: Box::new(Expr::Lit {
                            value: Literal::Number(idx as f64),
                            span: elem_span,
                        }),
                        span: elem_span,
                    };
                    self.desugar_pattern(sub, access, kind, decls);
                }
            }
        }
    }

    /// Parse `{pattern} = expr` or `[pattern] = expr` at declaration
    /// position and return the desugared flat list of declarators.
    fn parse_destructuring_decl(&mut self, kind: VarKind) -> Result<Vec<VarDeclarator>> {
        let pattern = self.parse_pattern()?;
        self.expect(&Token::Eq)?;
        let init = self.parse_assignment_expression()?;
        let mut decls = Vec::new();
        self.desugar_pattern(&pattern, init, kind, &mut decls);
        Ok(decls)
    }

    fn parse_var_declarator(&mut self, kind: VarKind) -> Result<VarDeclarator> {
        let start = self.current_span().start;

        let name = self.expect_ident()?;

        // Check for type annotation matching this variable name
        let type_annotation = self.try_get_type_annotation(self.current_span(), &name);

        let init = if self.consume_if(&Token::Eq) {
            Some(self.parse_assignment_expression()?)
        } else {
            None
        };

        let end = init
            .as_ref()
            .map(|e| e.span().end)
            .unwrap_or(self.prev_span().end);

        Ok(VarDeclarator {
            name,
            init,
            type_annotation,
            kind,
            span: Span::new(start, end),
        })
    }

    fn parse_import_declaration(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Import)?;

        // Check for side-effect import: import "module"
        if let Token::String(source) = self.current().clone() {
            self.advance();
            self.consume_semicolon();
            return Ok(Stmt::Import {
                specifiers: vec![],
                source,
                span: Span::new(start, self.prev_span().end),
            });
        }

        let mut specifiers = Vec::new();

        // Check for namespace import: import * as name from "module"
        if self.consume_if(&Token::Star) {
            self.expect(&Token::As)?;
            let local = self.expect_ident()?;
            let spec_span = Span::new(start, self.prev_span().end);
            specifiers.push(ImportSpecifier::Namespace {
                local,
                span: spec_span,
            });
        }
        // Check for default import: import name from "module"
        // or default + named: import name, { ... } from "module"
        else if let Token::Ident(_) = self.current() {
            // Don't consume identifier if next token is 'from' and this looks like
            // a misparse, or if we're looking at just a brace (named imports only)
            if !self.check(&Token::LBrace) {
                let local = self.expect_ident()?;
                let spec_span = Span::new(start, self.prev_span().end);
                specifiers.push(ImportSpecifier::Default {
                    local,
                    span: spec_span,
                });

                // If followed by comma, continue to parse named imports
                // Otherwise, go directly to 'from' clause
                if !self.consume_if(&Token::Comma) {
                    self.expect(&Token::From)?;
                    let source = self.expect_string()?;
                    self.consume_semicolon();
                    return Ok(Stmt::Import {
                        specifiers,
                        source,
                        span: Span::new(start, self.prev_span().end),
                    });
                }
                // If we consumed a comma, fall through to named imports parsing
            }
        }

        // Parse named imports: { a, b as c }
        if self.consume_if(&Token::LBrace) {
            while !self.check(&Token::RBrace) {
                let spec_start = self.current_span().start;
                let imported = self.expect_ident()?;

                let local = if self.consume_if(&Token::As) {
                    self.expect_ident()?
                } else {
                    imported.clone()
                };

                specifiers.push(ImportSpecifier::Named {
                    imported,
                    local,
                    span: Span::new(spec_start, self.prev_span().end),
                });

                if !self.consume_if(&Token::Comma) {
                    break;
                }
            }
            self.expect(&Token::RBrace)?;
        }

        self.expect(&Token::From)?;
        let source = self.expect_string()?;
        self.consume_semicolon();

        Ok(Stmt::Import {
            specifiers,
            source,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_export_declaration(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Export)?;

        // Check what we're exporting
        match self.current() {
            // `let` is treated as `var` for parsing purposes.
            Token::Var | Token::Let => {
                // export var x = 1;  (also: export let x = 1;)
                self.advance();
                let mut declarations = Vec::new();
                loop {
                    let decl = self.parse_var_declarator(VarKind::Var)?;
                    declarations.push(decl);
                    if !self.consume_if(&Token::Comma) {
                        break;
                    }
                }
                self.consume_semicolon();
                let decl_span = Span::new(start, self.prev_span().end);
                Ok(Stmt::Export {
                    declaration: ExportDecl::Var {
                        kind: VarKind::Var,
                        declarations,
                        span: decl_span,
                    },
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Token::Const => {
                // export const x = 1;
                self.advance();
                let mut declarations = Vec::new();
                loop {
                    let decl = self.parse_var_declarator(VarKind::Const)?;
                    declarations.push(decl);
                    if !self.consume_if(&Token::Comma) {
                        break;
                    }
                }
                self.consume_semicolon();
                let decl_span = Span::new(start, self.prev_span().end);
                Ok(Stmt::Export {
                    declaration: ExportDecl::Var {
                        kind: VarKind::Const,
                        declarations,
                        span: decl_span,
                    },
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Token::Function => {
                // export function foo() {}
                let func_start = self.current_span();
                self.advance();
                let name = self.expect_ident()?;
                // Check for type annotation matching this function name
                let type_annotation = self.try_get_type_annotation_for_function(func_start, &name);
                self.expect(&Token::LParen)?;
                let params = self.parse_parameters()?;
                self.expect(&Token::RParen)?;
                let body = Box::new(self.parse_function_body_block()?);
                let func_span = Span::new(start, self.prev_span().end);

                Ok(Stmt::Export {
                    declaration: ExportDecl::Function {
                        name,
                        params,
                        body,
                        type_annotation,
                        span: func_span,
                    },
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Token::Default => {
                // export default <function-expression-or-assignment-expression>
                self.advance();
                let value = if self.check(&Token::Function) {
                    self.parse_function_expression()?
                } else {
                    self.parse_assignment_expression()?
                };
                self.consume_semicolon();
                let decl_span = Span::new(start, self.prev_span().end);
                Ok(Stmt::Export {
                    declaration: ExportDecl::Default {
                        value,
                        span: decl_span,
                    },
                    span: decl_span,
                })
            }
            _ => Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: "var, const, function, or default".to_string(),
                span: self.current_span(),
            }
            .into()),
        }
    }

    fn expect_string(&mut self) -> Result<String> {
        if let Token::String(s) = self.current().clone() {
            self.advance();
            Ok(s)
        } else {
            Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: "string".to_string(),
                span: self.current_span(),
            }
            .into())
        }
    }

    /// Parse a class declaration and desugar it into a factory function.
    ///
    /// `class Counter { constructor(n) { this.value = n; } inc() { ... } }`
    /// becomes
    /// `function Counter(n) { return { value: n, inc: function() {...} }; }`.
    ///
    /// Extends/super, static methods and private fields are not supported.
    /// The constructor body must consist of `this.X = EXPR;` statements
    /// only — those become the initial field values of the returned object
    /// literal. Any other kind of constructor statement errors out; users
    /// who need more should write the factory function directly.
    fn parse_class_declaration(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Class)?;
        let name = self.expect_ident()?;

        // Reject `extends Parent` for now; it'd need a real prototype chain
        // to match runtime semantics and minfern has no inheritance.
        if self.check(&Token::Extends) {
            let span = self.current_span();
            return Err(ParseError::UnexpectedToken {
                found: "extends".to_string(),
                expected: "{ (class inheritance is not supported)".to_string(),
                span,
            }
            .into());
        }

        self.expect(&Token::LBrace)?;

        let mut ctor_params: Vec<String> = Vec::new();
        let mut field_props: Vec<PropDef> = Vec::new();
        let mut method_props: Vec<PropDef> = Vec::new();

        while !self.check(&Token::RBrace) && !self.is_at_end() {
            // Skip empty separators (class bodies don't require semicolons
            // between members but tolerate them).
            if self.consume_if(&Token::Semicolon) {
                continue;
            }

            let member_start = self.current_span().start;
            let key_name = self.expect_ident()?;
            let key_span = self.prev_span();

            // Explicitly unsupported prefixes. `static` would need function-
            // with-properties to model `Foo.bar()`; we have no inheritance
            // or prototype chain either, so reject at parse time.
            if key_name == "static" && matches!(self.current(), Token::Ident(_)) {
                return Err(ParseError::UnexpectedToken {
                    found: "static".to_string(),
                    expected: "instance method (static class members are not supported; see examples/spa/gaps.md)".to_string(),
                    span: key_span,
                }
                .into());
            }

            // `get name()` / `set name(param)` — accessor property. The
            // body is a block just like a method; we emit PropDef::Getter /
            // PropDef::Setter so the object-literal machinery types the
            // result as the getter's return and the setter's assignment
            // target.
            if (key_name == "get" || key_name == "set")
                && matches!(self.current(), Token::Ident(_))
            {
                let is_setter = key_name == "set";
                let accessor_name = self.expect_ident()?;
                self.expect(&Token::LParen)?;
                let (params, prefix) = self.parse_parameters_with_prefix()?;
                self.expect(&Token::RParen)?;
                let body = Self::prepend_param_destructuring(
                    self.parse_function_body_block()?,
                    prefix,
                );
                let member_span = Span::new(member_start, self.prev_span().end);
                let accessor = if is_setter {
                    if params.len() != 1 {
                        return Err(ParseError::UnexpectedToken {
                            found: format!("{} parameters", params.len()),
                            expected: "exactly one parameter for a setter".to_string(),
                            span: member_span,
                        }
                        .into());
                    }
                    PropDef::Setter {
                        key: PropKey::Ident(accessor_name),
                        param: params.into_iter().next().unwrap(),
                        body: Box::new(body),
                        span: member_span,
                    }
                } else {
                    if !params.is_empty() {
                        return Err(ParseError::UnexpectedToken {
                            found: format!("{} parameters", params.len()),
                            expected: "no parameters for a getter".to_string(),
                            span: member_span,
                        }
                        .into());
                    }
                    PropDef::Getter {
                        key: PropKey::Ident(accessor_name),
                        body: Box::new(body),
                        span: member_span,
                    }
                };
                method_props.push(accessor);
                continue;
            }

            self.expect(&Token::LParen)?;
            let params = self.parse_parameters()?;
            self.expect(&Token::RParen)?;
            let body_stmt = self.parse_function_body_block()?;
            let member_span = Span::new(member_start, self.prev_span().end);

            if key_name == "constructor" {
                ctor_params = params;
                // Extract field initialisations from the constructor body.
                let stmts = match &body_stmt {
                    Stmt::Block { body, .. } => body.clone(),
                    _ => vec![body_stmt.clone()],
                };
                for s in stmts {
                    match s {
                        Stmt::Expr { expression, .. } => {
                            if let Some((field, value, span)) =
                                Parser::extract_this_assignment(&expression)
                            {
                                field_props.push(PropDef::Property {
                                    key: PropKey::Ident(field),
                                    value,
                                    type_annotation: None,
                                    span,
                                });
                            } else {
                                return Err(ParseError::UnexpectedToken {
                                    found: "complex expression".to_string(),
                                    expected: "this.FIELD = EXPR; (constructor is limited to simple field initialisers)".to_string(),
                                    span: expression.span(),
                                }
                                .into());
                            }
                        }
                        other => {
                            return Err(ParseError::UnexpectedToken {
                                found: "statement".to_string(),
                                expected: "this.FIELD = EXPR; (constructor is limited to simple field initialisers)".to_string(),
                                span: other.span(),
                            }
                            .into());
                        }
                    }
                }
            } else {
                method_props.push(PropDef::Method {
                    key: PropKey::Ident(key_name),
                    params,
                    body: Box::new(body_stmt),
                    span: member_span,
                });
            }

            let _ = key_span; // kept only to document where the member name lived
        }

        self.expect(&Token::RBrace)?;
        let end = self.prev_span().end;
        let span = Span::new(start, end);

        // Build the object literal: field properties first, then methods.
        let mut all_props = field_props;
        all_props.extend(method_props);
        let obj_literal = Expr::Object {
            properties: all_props,
            span,
        };

        // Wrap the object literal in `function Name(ctor_params) { return <obj>; }`.
        let body_block = Stmt::Block {
            body: vec![Stmt::Return {
                argument: Some(obj_literal),
                span,
            }],
            span,
        };

        Ok(Stmt::FunctionDecl {
            name,
            params: ctor_params,
            body: Box::new(body_block),
            type_annotation: None,
            span,
        })
    }

    /// Match `this.FIELD = EXPR` exactly and return `(FIELD, EXPR, span)`.
    /// Any other expression returns None.
    fn extract_this_assignment(expr: &Expr) -> Option<(String, Expr, Span)> {
        if let Expr::Assign {
            op: AssignOp::Assign,
            left,
            right,
            span,
        } = expr
        {
            if let Expr::Member {
                object, property, ..
            } = left.as_ref()
            {
                if matches!(object.as_ref(), Expr::This { .. }) {
                    return Some((property.clone(), (**right).clone(), *span));
                }
            }
        }
        None
    }

    /// Wrap an `async function` declaration so its return type becomes
    /// `Promise<T>`. The body is lifted into an IIFE and handed to
    /// `Promise.resolve`, turning `async function foo(x) { return x + 1; }`
    /// into `function foo(x) { return Promise.resolve((function() { return x + 1; })()); }`.
    ///
    /// Inference then types `foo` as `(T) => Promise<T>` with no extra
    /// cases. `await e` inside the original body continues to be
    /// expressed via `UnaryOp::Await`, which the inference rule for
    /// unary ops turns into the inner type of its operand's `Promise<T>`.
    fn make_async_function_decl(decl: Stmt) -> Stmt {
        if let Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            span,
        } = decl
        {
            let new_body = Self::wrap_body_in_promise_resolve(body, span);
            Stmt::FunctionDecl {
                name,
                params,
                body: new_body,
                type_annotation,
                span,
            }
        } else {
            decl
        }
    }

    fn wrap_body_in_promise_resolve(body: Box<Stmt>, span: Span) -> Box<Stmt> {
        // (function () { ...body... })()
        let iife = Expr::Function {
            name: None,
            params: vec![],
            body,
            type_annotation: None,
            span,
        };
        let iife_call = Expr::Call {
            callee: Box::new(iife),
            arguments: vec![],
            span,
        };
        // Promise.resolve(<iife_call>)
        let resolve_call = Expr::Call {
            callee: Box::new(Expr::Member {
                object: Box::new(Expr::Ident {
                    name: "Promise".to_string(),
                    span,
                }),
                property: "resolve".to_string(),
                span,
            }),
            arguments: vec![iife_call],
            span,
        };
        // { return <resolve_call>; }
        Box::new(Stmt::Block {
            body: vec![Stmt::Return {
                argument: Some(resolve_call),
                span,
            }],
            span,
        })
    }

    fn parse_function_declaration(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        let func_span = self.current_span();

        self.expect(&Token::Function)?;

        let name = self.expect_ident()?;

        // Check for type annotation that matches this function name
        let type_annotation = self.try_get_type_annotation_for_function(func_span, &name);

        self.expect(&Token::LParen)?;
        let (params, prefix) = self.parse_parameters_with_prefix()?;
        self.expect(&Token::RParen)?;

        let body = Box::new(Self::prepend_param_destructuring(
            self.parse_function_body_block()?,
            prefix,
        ));

        Ok(Stmt::FunctionDecl {
            name,
            params,
            body,
            type_annotation,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Parse a comma-separated parameter list. A parameter may be a plain
    /// identifier or a destructuring pattern; pattern parameters synthesise
    /// a fresh temp name in the returned name list and emit the
    /// corresponding destructuring into `prefix_stmts`, which callers
    /// prepend to the function body.
    fn parse_parameters_with_prefix(
        &mut self,
    ) -> Result<(Vec<String>, Vec<Stmt>)> {
        let mut names = Vec::new();
        let mut prefix = Vec::new();

        if !self.check(&Token::RParen) {
            loop {
                if self.check(&Token::LBrace) || self.check(&Token::LBracket) {
                    let pattern = self.parse_pattern()?;
                    let temp = self.fresh_temp_name();
                    let pattern_span = Span::new(
                        self.prev_span().start,
                        self.prev_span().end,
                    );
                    let mut decls = Vec::new();
                    self.desugar_pattern(
                        &pattern,
                        Expr::Ident {
                            name: temp.clone(),
                            span: pattern_span,
                        },
                        VarKind::Var,
                        &mut decls,
                    );
                    prefix.push(Stmt::Var {
                        kind: VarKind::Var,
                        declarations: decls,
                        span: pattern_span,
                    });
                    names.push(temp);
                } else {
                    names.push(self.expect_ident()?);
                }

                if !self.consume_if(&Token::Comma) {
                    break;
                }
            }
        }

        Ok((names, prefix))
    }

    /// Parse a function body block, establishing a fresh async context.
    /// The body starts in an async context iff `next_fn_is_async` was set
    /// by the caller (e.g. the `async function` arm) — every other path
    /// starts at async_depth = 0, so `await` inside a plain function
    /// nested in an async one correctly errors.
    fn parse_function_body_block(&mut self) -> Result<Stmt> {
        let saved = self.async_depth;
        let is_async = std::mem::replace(&mut self.next_fn_is_async, false);
        self.async_depth = if is_async { 1 } else { 0 };
        let result = self.parse_block_statement();
        self.async_depth = saved;
        result
    }

    /// Thin wrapper for sites that know they don't have patterns (e.g.
    /// the deliberately-restricted class constructor parameters).
    fn parse_parameters(&mut self) -> Result<Vec<String>> {
        let (names, prefix) = self.parse_parameters_with_prefix()?;
        if !prefix.is_empty() {
            let span = prefix[0].span();
            return Err(ParseError::UnexpectedToken {
                found: "destructuring pattern".to_string(),
                expected: "plain parameter name".to_string(),
                span,
            }
            .into());
        }
        Ok(names)
    }

    /// Given a function body and any destructuring statements synthesised
    /// from pattern parameters, prepend them inside the body's block.
    fn prepend_param_destructuring(body: Stmt, prefix: Vec<Stmt>) -> Stmt {
        if prefix.is_empty() {
            return body;
        }
        match body {
            Stmt::Block {
                body: mut stmts,
                span,
            } => {
                let mut new_stmts = prefix;
                new_stmts.append(&mut stmts);
                Stmt::Block {
                    body: new_stmts,
                    span,
                }
            }
            other => {
                let span = other.span();
                let mut new_stmts = prefix;
                new_stmts.push(other);
                Stmt::Block {
                    body: new_stmts,
                    span,
                }
            }
        }
    }

    fn parse_if_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::If)?;
        self.expect(&Token::LParen)?;

        let test = self.parse_expression()?;

        self.expect(&Token::RParen)?;

        let consequent = Box::new(self.parse_statement()?);

        let alternate = if self.consume_if(&Token::Else) {
            Some(Box::new(self.parse_statement()?))
        } else {
            None
        };

        let end = alternate
            .as_ref()
            .map(|s| s.span().end)
            .unwrap_or(consequent.span().end);

        Ok(Stmt::If {
            test,
            consequent,
            alternate,
            span: Span::new(start, end),
        })
    }

    fn parse_while_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::While)?;
        self.expect(&Token::LParen)?;

        let test = self.parse_expression()?;

        self.expect(&Token::RParen)?;

        let body = Box::new(self.parse_statement()?);

        Ok(Stmt::While {
            test,
            body,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_do_while_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Do)?;

        let body = Box::new(self.parse_statement()?);

        self.expect(&Token::While)?;
        self.expect(&Token::LParen)?;

        let test = self.parse_expression()?;

        self.expect(&Token::RParen)?;
        self.consume_semicolon();

        Ok(Stmt::DoWhile {
            body,
            test,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_for_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::For)?;
        self.expect(&Token::LParen)?;

        // Parse init. `let i` in a for-init is treated identically to `var i`.
        let init_or_lhs = if self.check(&Token::Var) || self.check(&Token::Let) {
            let var_start = self.current_span().start;
            self.advance();

            // `for (let {a, b} of arr) { ... }` — a destructuring pattern
            // on the LHS. We desugar to a for-of over a synthesised temp,
            // prepending a destructuring declaration at the top of the
            // loop body so the pattern's bindings are in scope.
            if self.check(&Token::LBrace) || self.check(&Token::LBracket) {
                let pattern = self.parse_pattern()?;
                if self.check(&Token::In) || self.check(&Token::Of) {
                    let is_of = self.check(&Token::Of);
                    self.advance();
                    let right = self.parse_expression()?;
                    self.expect(&Token::RParen)?;
                    let body = self.parse_statement()?;

                    let temp = self.fresh_temp_name();
                    let pattern_span = Span::new(var_start, self.prev_span().end);
                    // Build the destructuring declarations, initialised from
                    // the synthesised temp name.
                    let mut destr_decls = Vec::new();
                    self.desugar_pattern(
                        &pattern,
                        Expr::Ident {
                            name: temp.clone(),
                            span: pattern_span,
                        },
                        VarKind::Var,
                        &mut destr_decls,
                    );
                    let destr_stmt = Stmt::Var {
                        kind: VarKind::Var,
                        declarations: destr_decls,
                        span: pattern_span,
                    };

                    // Prepend the destructuring to the body.
                    let new_body = match body {
                        Stmt::Block {
                            body: mut body_stmts,
                            span: body_span,
                        } => {
                            let mut new_stmts = Vec::with_capacity(body_stmts.len() + 1);
                            new_stmts.push(destr_stmt);
                            new_stmts.append(&mut body_stmts);
                            Stmt::Block {
                                body: new_stmts,
                                span: body_span,
                            }
                        }
                        other => {
                            let body_span = other.span();
                            Stmt::Block {
                                body: vec![destr_stmt, other],
                                span: body_span,
                            }
                        }
                    };

                    let for_span = Span::new(start, self.prev_span().end);
                    return if is_of {
                        Ok(Stmt::ForOf {
                            left: ForInLhs::VarDecl(temp, None, pattern_span),
                            right,
                            body: Box::new(new_body),
                            span: for_span,
                        })
                    } else {
                        Ok(Stmt::ForIn {
                            left: ForInLhs::VarDecl(temp, None, pattern_span),
                            right,
                            body: Box::new(new_body),
                            span: for_span,
                        })
                    };
                } else {
                    // Destructuring in a C-style `for (init; test; update)`
                    // head would bind names only used for one iteration,
                    // which rarely makes sense. Reject and point the user
                    // at the for-of form.
                    let span = self.current_span();
                    return Err(ParseError::UnexpectedToken {
                        found: format!("{}", self.current()),
                        expected: "'of' or 'in' (destructuring pattern is only supported in for-of/for-in)".to_string(),
                        span,
                    }
                    .into());
                }
            }

            let name = self.expect_ident()?;
            let var_end = self.prev_span().end;
            let type_annotation = self.try_get_type_annotation(self.current_span(), &name);
            let var_span = Span::new(var_start, var_end);

            // Check for for-in/of
            if self.check(&Token::In) || self.check(&Token::Of) {
                let is_of = self.check(&Token::Of);
                self.advance();

                let right = self.parse_expression()?;
                self.expect(&Token::RParen)?;

                let body = Box::new(self.parse_statement()?);

                return if is_of {
                    Ok(Stmt::ForOf {
                        left: ForInLhs::VarDecl(name, type_annotation, var_span),
                        right,
                        body,
                        span: Span::new(start, self.prev_span().end),
                    })
                } else {
                    Ok(Stmt::ForIn {
                        left: ForInLhs::VarDecl(name, type_annotation, var_span),
                        right,
                        body,
                        span: Span::new(start, self.prev_span().end),
                    })
                };
            }

            // Regular for loop with var
            let init = if self.consume_if(&Token::Eq) {
                Some(self.parse_assignment_expression()?)
            } else {
                None
            };

            let mut declarations = vec![VarDeclarator {
                name,
                init,
                type_annotation,
                kind: VarKind::Var,
                span: Span::new(var_start, self.prev_span().end),
            }];

            while self.consume_if(&Token::Comma) {
                declarations.push(self.parse_var_declarator(VarKind::Var)?);
            }

            Some(ForInit::VarDecl(declarations))
        } else if self.check(&Token::Semicolon) {
            None
        } else {
            // Use no_in to prevent 'in' being parsed as binary operator
            let expr = self.parse_expression_no_in()?;

            // Check for for-in/of
            if self.check(&Token::In) || self.check(&Token::Of) {
                let is_of = self.check(&Token::Of);
                self.advance();

                let right = self.parse_expression()?;
                self.expect(&Token::RParen)?;

                let body = Box::new(self.parse_statement()?);

                return if is_of {
                    Ok(Stmt::ForOf {
                        left: ForInLhs::Expr(expr),
                        right,
                        body,
                        span: Span::new(start, self.prev_span().end),
                    })
                } else {
                    Ok(Stmt::ForIn {
                        left: ForInLhs::Expr(expr),
                        right,
                        body,
                        span: Span::new(start, self.prev_span().end),
                    })
                };
            }

            Some(ForInit::Expr(expr))
        };

        // Regular for loop
        self.expect(&Token::Semicolon)?;

        let test = if self.check(&Token::Semicolon) {
            None
        } else {
            Some(self.parse_expression()?)
        };

        self.expect(&Token::Semicolon)?;

        let update = if self.check(&Token::RParen) {
            None
        } else {
            Some(self.parse_expression()?)
        };

        self.expect(&Token::RParen)?;

        let body = Box::new(self.parse_statement()?);

        Ok(Stmt::For {
            init: init_or_lhs,
            test,
            update,
            body,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_return_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Return)?;

        let argument = if self.check(&Token::Semicolon) || self.is_at_end() {
            None
        } else {
            Some(self.parse_expression()?)
        };

        self.consume_semicolon();

        Ok(Stmt::Return {
            argument,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_throw_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Throw)?;

        let argument = self.parse_expression()?;
        self.consume_semicolon();

        Ok(Stmt::Throw {
            argument,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_try_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Try)?;

        let block = Box::new(self.parse_block_statement()?);

        let handler = if self.consume_if(&Token::Catch) {
            let catch_start = self.prev_span().start;
            self.expect(&Token::LParen)?;
            let param = self.expect_ident()?;
            self.expect(&Token::RParen)?;
            let body = Box::new(self.parse_block_statement()?);

            Some(CatchClause {
                param,
                body,
                span: Span::new(catch_start, self.prev_span().end),
            })
        } else {
            None
        };

        let finalizer = if self.consume_if(&Token::Finally) {
            Some(Box::new(self.parse_block_statement()?))
        } else {
            None
        };

        Ok(Stmt::Try {
            block,
            handler,
            finalizer,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_switch_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Switch)?;
        self.expect(&Token::LParen)?;

        let discriminant = self.parse_expression()?;

        self.expect(&Token::RParen)?;
        self.expect(&Token::LBrace)?;

        let mut cases = Vec::new();

        while !self.check(&Token::RBrace) && !self.is_at_end() {
            let case_start = self.current_span().start;

            let test = if self.consume_if(&Token::Case) {
                Some(self.parse_expression()?)
            } else {
                self.expect(&Token::Default)?;
                None
            };

            self.expect(&Token::Colon)?;

            let mut consequent = Vec::new();
            while !self.check(&Token::Case)
                && !self.check(&Token::Default)
                && !self.check(&Token::RBrace)
                && !self.is_at_end()
            {
                consequent.push(self.parse_statement()?);
            }

            let case_end = consequent
                .last()
                .map(|s| s.span().end)
                .unwrap_or(self.prev_span().end);

            cases.push(SwitchCase {
                test,
                consequent,
                span: Span::new(case_start, case_end),
            });
        }

        self.expect(&Token::RBrace)?;

        Ok(Stmt::Switch {
            discriminant,
            cases,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_break_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Break)?;

        let label = if let Token::Ident(name) = self.current() {
            let name = name.clone();
            self.advance();
            Some(name)
        } else {
            None
        };

        self.consume_semicolon();

        Ok(Stmt::Break {
            label,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_continue_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Continue)?;

        let label = if let Token::Ident(name) = self.current() {
            let name = name.clone();
            self.advance();
            Some(name)
        } else {
            None
        };

        self.consume_semicolon();

        Ok(Stmt::Continue {
            label,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_labeled_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        let label = self.expect_ident()?;
        self.expect(&Token::Colon)?;

        let body = Box::new(self.parse_statement()?);

        Ok(Stmt::Labeled {
            label,
            body,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_expression_statement(&mut self) -> Result<Stmt> {
        let start = self.current_span().start;
        let expression = self.parse_expression()?;
        self.consume_semicolon();

        Ok(Stmt::Expr {
            expression,
            span: Span::new(start, self.prev_span().end),
        })
    }

    // ========== Expression Parsing (Pratt Parser) ==========

    fn parse_expression(&mut self) -> Result<Expr> {
        self.parse_sequence_expression()
    }

    fn parse_sequence_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        let mut expr = self.parse_assignment_expression()?;

        if self.check(&Token::Comma) {
            let mut expressions = vec![expr];

            while self.consume_if(&Token::Comma) {
                expressions.push(self.parse_assignment_expression()?);
            }

            let end = expressions.last().unwrap().span().end;

            expr = Expr::Sequence {
                expressions,
                span: Span::new(start, end),
            };
        }

        Ok(expr)
    }

    fn parse_assignment_expression(&mut self) -> Result<Expr> {
        // Arrow functions are the only expression whose start overlaps with
        // a parenthesised expression or a bare identifier, so we look ahead
        // for a `=>` and take that path before falling back to the regular
        // assignment grammar.
        if self.looks_like_arrow_function() {
            return self.parse_arrow_function();
        }

        let expr = self.parse_conditional_expression()?;

        if let Some(op) = self.assignment_op() {
            let span = expr.span();
            if !expr.is_valid_assignment_target() {
                return Err(ParseError::InvalidAssignmentTarget { span }.into());
            }

            self.advance();
            let right = self.parse_assignment_expression()?;

            return Ok(Expr::Assign {
                op,
                left: Box::new(expr),
                right: Box::new(right),
                span: Span::new(span.start, self.prev_span().end),
            });
        }

        Ok(expr)
    }

    fn assignment_op(&self) -> Option<AssignOp> {
        match self.current() {
            Token::Eq => Some(AssignOp::Assign),
            Token::PlusEq => Some(AssignOp::AddAssign),
            Token::MinusEq => Some(AssignOp::SubAssign),
            Token::StarEq => Some(AssignOp::MulAssign),
            Token::StarStarEq => Some(AssignOp::PowAssign),
            Token::SlashEq => Some(AssignOp::DivAssign),
            Token::PercentEq => Some(AssignOp::ModAssign),
            Token::LShiftEq => Some(AssignOp::LShiftAssign),
            Token::RShiftEq => Some(AssignOp::RShiftAssign),
            Token::URShiftEq => Some(AssignOp::URShiftAssign),
            Token::BitAndEq => Some(AssignOp::BitAndAssign),
            Token::BitOrEq => Some(AssignOp::BitOrAssign),
            Token::BitXorEq => Some(AssignOp::BitXorAssign),
            _ => None,
        }
    }

    fn parse_conditional_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        let test = self.parse_binary_expression(0)?;

        if self.consume_if(&Token::Question) {
            let consequent = self.parse_assignment_expression()?;
            self.expect(&Token::Colon)?;
            let alternate = self.parse_assignment_expression()?;

            return Ok(Expr::Conditional {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate: Box::new(alternate),
                span: Span::new(start, self.prev_span().end),
            });
        }

        Ok(test)
    }

    fn parse_binary_expression(&mut self, min_prec: u8) -> Result<Expr> {
        let mut left = self.parse_unary_expression()?;

        while let Some(op) = self.binary_op() {
            let prec = op.precedence();
            if prec < min_prec {
                break;
            }

            self.advance();

            let next_min_prec = if op.is_right_assoc() { prec } else { prec + 1 };
            let right = self.parse_binary_expression(next_min_prec)?;

            let span = Span::new(left.span().start, right.span().end);
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
                span,
            };
        }

        Ok(left)
    }

    fn binary_op(&self) -> Option<BinOp> {
        match self.current() {
            Token::Plus => Some(BinOp::Add),
            Token::Minus => Some(BinOp::Sub),
            Token::Star => Some(BinOp::Mul),
            Token::StarStar => Some(BinOp::Pow),
            Token::Slash => Some(BinOp::Div),
            Token::Percent => Some(BinOp::Mod),
            Token::Lt => Some(BinOp::Lt),
            Token::Gt => Some(BinOp::Gt),
            Token::LtEq => Some(BinOp::LtEq),
            Token::GtEq => Some(BinOp::GtEq),
            Token::EqEq => Some(BinOp::EqEq),
            Token::NotEq => Some(BinOp::NotEq),
            Token::EqEqEq => Some(BinOp::EqEqEq),
            Token::NotEqEq => Some(BinOp::NotEqEq),
            Token::And => Some(BinOp::And),
            Token::Or => Some(BinOp::Or),
            Token::BitAnd => Some(BinOp::BitAnd),
            Token::BitOr => Some(BinOp::BitOr),
            Token::BitXor => Some(BinOp::BitXor),
            Token::LShift => Some(BinOp::LShift),
            Token::RShift => Some(BinOp::RShift),
            Token::URShift => Some(BinOp::URShift),
            Token::In if !self.no_in => Some(BinOp::In),
            Token::Instanceof => Some(BinOp::Instanceof),
            _ => None,
        }
    }

    fn parse_unary_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        // Prefix operators
        let op = match self.current() {
            Token::Minus => Some(UnaryOp::Neg),
            Token::Plus => Some(UnaryOp::Pos),
            Token::Not => Some(UnaryOp::Not),
            Token::BitNot => Some(UnaryOp::BitNot),
            Token::Typeof => Some(UnaryOp::Typeof),
            Token::Void => Some(UnaryOp::Void),
            Token::Delete => Some(UnaryOp::Delete),
            Token::Await => Some(UnaryOp::Await),
            Token::PlusPlus => Some(UnaryOp::PreInc),
            Token::MinusMinus => Some(UnaryOp::PreDec),
            _ => None,
        };

        if let Some(op) = op {
            // `await` is a parse error outside of an async function body.
            // Keyword tokens are what trigger this branch, so a stray
            // `await` in a regular function already fails — we just give
            // a nicer message.
            if matches!(op, UnaryOp::Await) && self.async_depth == 0 {
                let span = self.current_span();
                return Err(ParseError::UnexpectedToken {
                    found: "await".to_string(),
                    expected: "expression (await is only valid inside an async function)".to_string(),
                    span,
                }
                .into());
            }
            self.advance();
            let argument = self.parse_unary_expression()?;

            return Ok(Expr::Unary {
                op,
                argument: Box::new(argument),
                span: Span::new(start, self.prev_span().end),
            });
        }

        self.parse_postfix_expression()
    }

    fn parse_postfix_expression(&mut self) -> Result<Expr> {
        let mut expr = self.parse_call_expression()?;

        // Postfix ++/--
        match self.current() {
            Token::PlusPlus => {
                let span = Span::new(expr.span().start, self.current_span().end);
                self.advance();
                expr = Expr::Unary {
                    op: UnaryOp::PostInc,
                    argument: Box::new(expr),
                    span,
                };
            }
            Token::MinusMinus => {
                let span = Span::new(expr.span().start, self.current_span().end);
                self.advance();
                expr = Expr::Unary {
                    op: UnaryOp::PostDec,
                    argument: Box::new(expr),
                    span,
                };
            }
            _ => {}
        }

        Ok(expr)
    }

    fn parse_call_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        // Handle 'new' expression
        if self.consume_if(&Token::New) {
            // Check for new.target
            if self.consume_if(&Token::Dot) {
                self.expect_keyword("target")?;
                return Ok(Expr::NewTarget {
                    span: Span::new(start, self.prev_span().end),
                });
            }

            let callee = self.parse_member_expression()?;

            let arguments = if self.consume_if(&Token::LParen) {
                self.parse_arguments()?
            } else {
                Vec::new()
            };

            return Ok(Expr::New {
                callee: Box::new(callee),
                arguments,
                span: Span::new(start, self.prev_span().end),
            });
        }

        let mut expr = self.parse_member_expression()?;

        // Handle call and member expressions
        loop {
            if self.consume_if(&Token::LParen) {
                let arguments = self.parse_arguments()?;
                expr = Expr::Call {
                    callee: Box::new(expr),
                    arguments,
                    span: Span::new(start, self.prev_span().end),
                };
            } else if self.consume_if(&Token::Dot) {
                let property = self.expect_ident_or_keyword()?;
                expr = Expr::Member {
                    object: Box::new(expr),
                    property,
                    span: Span::new(start, self.prev_span().end),
                };
            } else if self.consume_if(&Token::LBracket) {
                let property = self.parse_expression()?;
                self.expect(&Token::RBracket)?;
                expr = Expr::ComputedMember {
                    object: Box::new(expr),
                    property: Box::new(property),
                    span: Span::new(start, self.prev_span().end),
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_member_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        let mut expr = self.parse_primary_expression()?;

        loop {
            if self.consume_if(&Token::Dot) {
                let property = self.expect_ident_or_keyword()?;
                expr = Expr::Member {
                    object: Box::new(expr),
                    property,
                    span: Span::new(start, self.prev_span().end),
                };
            } else if self.consume_if(&Token::LBracket) {
                let property = self.parse_expression()?;
                self.expect(&Token::RBracket)?;
                expr = Expr::ComputedMember {
                    object: Box::new(expr),
                    property: Box::new(property),
                    span: Span::new(start, self.prev_span().end),
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_arguments(&mut self) -> Result<Vec<Expr>> {
        let mut args = Vec::new();

        if !self.check(&Token::RParen) {
            loop {
                args.push(self.parse_assignment_expression()?);

                if !self.consume_if(&Token::Comma) {
                    break;
                }
            }
        }

        self.expect(&Token::RParen)?;
        Ok(args)
    }

    fn parse_primary_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        match self.current().clone() {
            Token::This => {
                self.advance();
                Ok(Expr::This {
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::Ident(name) => {
                self.advance();
                Ok(Expr::Ident {
                    name,
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::Number(n) => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Number(n),
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::String(s) => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::String(s),
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::True => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Boolean(true),
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::False => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Boolean(false),
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::Null => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Null,
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::Regex { pattern, flags } => {
                self.advance();
                Ok(Expr::Lit {
                    value: Literal::Regex { pattern, flags },
                    span: Span::new(start, self.prev_span().end),
                })
            }

            Token::LParen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(&Token::RParen)?;
                Ok(expr)
            }

            Token::LBracket => self.parse_array_literal(),

            Token::LBrace => self.parse_object_literal(),

            Token::Function => self.parse_function_expression(),

            Token::TemplateNoSub(_) | Token::TemplateHead(_) => self.parse_template_literal(),

            _ => {
                let span = self.current_span();
                Err(ParseError::UnexpectedToken {
                    found: format!("{}", self.current()),
                    expected: "expression".to_string(),
                    span,
                }
                .into())
            }
        }
    }

    fn parse_template_literal(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        match self.current().clone() {
            Token::TemplateNoSub(s) => {
                // Simple template with no substitutions
                self.advance();
                Ok(Expr::TemplateLiteral {
                    quasis: vec![s],
                    expressions: vec![],
                    span: Span::new(start, self.prev_span().end),
                })
            }
            Token::TemplateHead(s) => {
                // Template with substitutions
                self.advance();
                let mut quasis = vec![s];
                let mut expressions = Vec::new();

                loop {
                    // Parse the expression inside ${}
                    let expr = self.parse_expression()?;
                    expressions.push(expr);

                    // Expect either TemplateMiddle or TemplateTail
                    match self.current().clone() {
                        Token::TemplateMiddle(s) => {
                            self.advance();
                            quasis.push(s);
                            // Continue to next expression
                        }
                        Token::TemplateTail(s) => {
                            self.advance();
                            quasis.push(s);
                            break;
                        }
                        _ => {
                            return Err(ParseError::UnexpectedToken {
                                found: format!("{}", self.current()),
                                expected: "template continuation".to_string(),
                                span: self.current_span(),
                            }
                            .into());
                        }
                    }
                }

                Ok(Expr::TemplateLiteral {
                    quasis,
                    expressions,
                    span: Span::new(start, self.prev_span().end),
                })
            }
            _ => unreachable!("parse_template_literal called with non-template token"),
        }
    }

    fn parse_array_literal(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        self.expect(&Token::LBracket)?;

        let mut elements = Vec::new();

        while !self.check(&Token::RBracket) {
            if self.check(&Token::Comma) {
                // Hole in array
                elements.push(None);
            } else {
                elements.push(Some(self.parse_assignment_expression()?));
            }

            if !self.consume_if(&Token::Comma) {
                break;
            }
        }

        self.expect(&Token::RBracket)?;

        Ok(Expr::Array {
            elements,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_object_literal(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        self.expect(&Token::LBrace)?;

        let mut properties = Vec::new();

        while !self.check(&Token::RBrace) {
            properties.push(self.parse_property_definition()?);

            if !self.consume_if(&Token::Comma) {
                break;
            }
        }

        self.expect(&Token::RBrace)?;

        Ok(Expr::Object {
            properties,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_property_definition(&mut self) -> Result<PropDef> {
        let start = self.current_span().start;

        // Check for getter/setter
        // Must be: get/set followed by property key (not : or ()
        if let Token::Ident(name) = self.current().clone() {
            if name == "get" && !self.peek_is(&Token::Colon) && !self.peek_is(&Token::LParen) {
                self.advance();
                let key = self.parse_property_key()?;
                self.expect(&Token::LParen)?;
                self.expect(&Token::RParen)?;
                let body = Box::new(self.parse_function_body_block()?);

                return Ok(PropDef::Getter {
                    key,
                    body,
                    span: Span::new(start, self.prev_span().end),
                });
            }

            if name == "set" && !self.peek_is(&Token::Colon) && !self.peek_is(&Token::LParen) {
                self.advance();
                let key = self.parse_property_key()?;
                self.expect(&Token::LParen)?;
                let param = self.expect_ident()?;
                self.expect(&Token::RParen)?;
                let body = Box::new(self.parse_function_body_block()?);

                return Ok(PropDef::Setter {
                    key,
                    param,
                    body,
                    span: Span::new(start, self.prev_span().end),
                });
            }
        }

        let key = self.parse_property_key()?;

        // Check for method shorthand
        if self.check(&Token::LParen) {
            self.advance();
            let (params, prefix) = self.parse_parameters_with_prefix()?;
            self.expect(&Token::RParen)?;
            let body = Box::new(Self::prepend_param_destructuring(
                self.parse_function_body_block()?,
                prefix,
            ));

            return Ok(PropDef::Method {
                key,
                params,
                body,
                span: Span::new(start, self.prev_span().end),
            });
        }

        // Per-field type annotation: `key /*: T */: value`. We look it up by
        // the key name *before* consuming the colon, so the scanner's
        // `last_ident = key` at the time of the `/*:` lines up.
        let type_annotation = if let PropKey::Ident(name) = &key {
            self.try_get_type_annotation(self.current_span(), name)
        } else {
            None
        };

        // Regular property
        self.expect(&Token::Colon)?;
        let value = self.parse_assignment_expression()?;

        Ok(PropDef::Property {
            key,
            value,
            type_annotation,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_property_key(&mut self) -> Result<PropKey> {
        match self.current().clone() {
            Token::Ident(name) => {
                self.advance();
                Ok(PropKey::Ident(name))
            }
            Token::String(s) => {
                self.advance();
                Ok(PropKey::String(s))
            }
            Token::Number(n) => {
                self.advance();
                Ok(PropKey::Number(n))
            }
            // Allow keywords as property names
            tok if self.is_keyword(&tok) => {
                let name = self.keyword_to_string(&tok);
                self.advance();
                Ok(PropKey::Ident(name))
            }
            _ => {
                let span = self.current_span();
                Err(ParseError::UnexpectedToken {
                    found: format!("{}", self.current()),
                    expected: "property name".to_string(),
                    span,
                }
                .into())
            }
        }
    }

    /// Check if a token is a keyword
    fn is_keyword(&self, token: &Token) -> bool {
        matches!(
            token,
            Token::Var
                | Token::Let
                | Token::Const
                | Token::Function
                | Token::If
                | Token::Else
                | Token::While
                | Token::Do
                | Token::For
                | Token::In
                | Token::Of
                | Token::Return
                | Token::Throw
                | Token::Try
                | Token::Catch
                | Token::Finally
                | Token::Switch
                | Token::Case
                | Token::Default
                | Token::Break
                | Token::Continue
                | Token::New
                | Token::Delete
                | Token::Typeof
                | Token::Void
                | Token::Instanceof
                | Token::This
                | Token::Null
                | Token::True
                | Token::False
                | Token::Import
                | Token::Export
                | Token::From
                | Token::As
        )
    }

    /// Convert a keyword token to its string representation
    fn keyword_to_string(&self, token: &Token) -> String {
        match token {
            Token::Var => "var",
            Token::Let => "let",
            Token::Const => "const",
            Token::Function => "function",
            Token::If => "if",
            Token::Else => "else",
            Token::While => "while",
            Token::Do => "do",
            Token::For => "for",
            Token::In => "in",
            Token::Of => "of",
            Token::Return => "return",
            Token::Throw => "throw",
            Token::Try => "try",
            Token::Catch => "catch",
            Token::Finally => "finally",
            Token::Switch => "switch",
            Token::Case => "case",
            Token::Default => "default",
            Token::Break => "break",
            Token::Continue => "continue",
            Token::New => "new",
            Token::Delete => "delete",
            Token::Typeof => "typeof",
            Token::Void => "void",
            Token::Instanceof => "instanceof",
            Token::This => "this",
            Token::Null => "null",
            Token::True => "true",
            Token::False => "false",
            Token::Import => "import",
            Token::Export => "export",
            Token::From => "from",
            Token::As => "as",
            Token::Class => "class",
            Token::Extends => "extends",
            Token::Super => "super",
            Token::Async => "async",
            Token::Await => "await",
            _ => unreachable!("keyword_to_string called on non-keyword"),
        }
        .to_string()
    }

    /// Lookahead: is the token stream at this point the head of an arrow
    /// function? Accepts `ident =>`, `() =>`, and `(ident [, ident]*) =>`.
    /// Does not consume anything.
    fn looks_like_arrow_function(&self) -> bool {
        // Simple param: `ident =>`
        if matches!(self.current(), Token::Ident(_)) {
            return self.tokens
                .get(self.pos + 1)
                .map(|s| matches!(s.value, Token::FatArrow))
                .unwrap_or(false);
        }

        // Parenthesised params: `(` ... `)` `=>`. We only need to know
        // whether the matching `)` is immediately followed by `=>`, so we
        // track nesting for every kind of bracket and ignore everything
        // else. Pattern parameters (`({x})`, `([a, b])`) go through here
        // just fine — the inner braces/brackets are balanced like any
        // other group.
        if matches!(self.current(), Token::LParen) {
            let mut i = self.pos + 1;
            let mut paren_depth: i32 = 1;
            let mut brace_depth: i32 = 0;
            let mut bracket_depth: i32 = 0;
            while let Some(tok) = self.tokens.get(i) {
                match &tok.value {
                    Token::LParen => paren_depth += 1,
                    Token::RParen => {
                        paren_depth -= 1;
                        if paren_depth == 0 && brace_depth == 0 && bracket_depth == 0 {
                            return self.tokens
                                .get(i + 1)
                                .map(|s| matches!(s.value, Token::FatArrow))
                                .unwrap_or(false);
                        }
                    }
                    Token::LBrace => brace_depth += 1,
                    Token::RBrace => brace_depth -= 1,
                    Token::LBracket => bracket_depth += 1,
                    Token::RBracket => bracket_depth -= 1,
                    Token::Eof => return false,
                    _ => {}
                }
                i += 1;
            }
            return false;
        }

        false
    }

    /// Parse an arrow function. Called after [`looks_like_arrow_function`]
    /// has confirmed we're at the head of one, so all of the error paths
    /// below correspond to an actual malformed arrow.
    ///
    /// Lowers to `Expr::Function`: a block body becomes the function body
    /// directly, an expression body becomes a synthesised `return <expr>;`.
    fn parse_arrow_function(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        // Parse parameters.
        let (params, prefix): (Vec<String>, Vec<Stmt>) =
            if matches!(self.current(), Token::Ident(_)) {
                // Single-identifier form: `x => ...`
                let name = self.expect_ident()?;
                (vec![name], vec![])
            } else {
                self.expect(&Token::LParen)?;
                let result = self.parse_parameters_with_prefix()?;
                self.expect(&Token::RParen)?;
                result
            };

        self.expect(&Token::FatArrow)?;

        // Arrow functions establish their own function body scope, same
        // as any other callable form. Non-async arrows reset async_depth
        // to 0 for the duration of their body, which correctly rejects
        // `await` inside an arrow nested in a regular function.
        let saved_async = self.async_depth;
        let is_async = std::mem::replace(&mut self.next_fn_is_async, false);
        self.async_depth = if is_async { 1 } else { 0 };

        // Body: block `{ ... }` or a single expression.
        let body = if self.check(&Token::LBrace) {
            Box::new(Self::prepend_param_destructuring(
                self.parse_block_statement()?,
                prefix,
            ))
        } else {
            let expr_start = self.current_span().start;
            let expr = self.parse_assignment_expression()?;
            let expr_end = self.prev_span().end;
            let return_span = Span::new(expr_start, expr_end);
            let mut stmts = prefix;
            stmts.push(Stmt::Return {
                argument: Some(expr),
                span: return_span,
            });
            Box::new(Stmt::Block {
                body: stmts,
                span: return_span,
            })
        };

        self.async_depth = saved_async;

        Ok(Expr::Function {
            name: None,
            params,
            body,
            type_annotation: None,
            span: Span::new(start, self.prev_span().end),
        })
    }

    fn parse_function_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        let func_span = self.current_span();

        self.expect(&Token::Function)?;

        let name = if let Token::Ident(name) = self.current().clone() {
            self.advance();
            Some(name)
        } else {
            None
        };

        // Check for type annotation if function has a name
        let type_annotation = if let Some(ref n) = name {
            self.try_get_type_annotation_for_function(func_span, n)
        } else {
            None
        };

        self.expect(&Token::LParen)?;
        let (params, prefix) = self.parse_parameters_with_prefix()?;
        self.expect(&Token::RParen)?;

        let body = Box::new(Self::prepend_param_destructuring(
            self.parse_function_body_block()?,
            prefix,
        ));

        Ok(Expr::Function {
            name,
            params,
            body,
            type_annotation,
            span: Span::new(start, self.prev_span().end),
        })
    }

    // ========== Helper Methods ==========

    fn current(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .map(|s| &s.value)
            .unwrap_or(&Token::Eof)
    }

    fn current_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|s| s.span)
            .unwrap_or(Span::default())
    }

    fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens
                .get(self.pos - 1)
                .map(|s| s.span)
                .unwrap_or(Span::default())
        } else {
            Span::default()
        }
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn is_at_end(&self) -> bool {
        self.current() == &Token::Eof
    }

    fn check(&self, token: &Token) -> bool {
        std::mem::discriminant(self.current()) == std::mem::discriminant(token)
    }

    fn peek_is(&self, token: &Token) -> bool {
        self.tokens
            .get(self.pos + 1)
            .map(|s| std::mem::discriminant(&s.value) == std::mem::discriminant(token))
            .unwrap_or(false)
    }

    fn consume_if(&mut self, token: &Token) -> bool {
        if self.check(token) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, token: &Token) -> Result<()> {
        if self.check(token) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: format!("{}", token),
                span: self.current_span(),
            }
            .into())
        }
    }

    fn expect_ident(&mut self) -> Result<String> {
        if let Token::Ident(name) = self.current().clone() {
            self.advance();
            Ok(name)
        } else {
            Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: "identifier".to_string(),
                span: self.current_span(),
            }
            .into())
        }
    }

    /// Expect an identifier or keyword (for member access like obj.if)
    fn expect_ident_or_keyword(&mut self) -> Result<String> {
        match self.current().clone() {
            Token::Ident(name) => {
                self.advance();
                Ok(name)
            }
            tok if self.is_keyword(&tok) => {
                let name = self.keyword_to_string(&tok);
                self.advance();
                Ok(name)
            }
            _ => Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: "identifier or keyword".to_string(),
                span: self.current_span(),
            }
            .into()),
        }
    }

    fn expect_keyword(&mut self, kw: &str) -> Result<()> {
        if let Token::Ident(name) = self.current() {
            if name == kw {
                self.advance();
                return Ok(());
            }
        }
        Err(ParseError::UnexpectedToken {
            found: format!("{}", self.current()),
            expected: kw.to_string(),
            span: self.current_span(),
        }
        .into())
    }

    fn consume_semicolon(&mut self) {
        // Automatic semicolon insertion - just consume if present
        self.consume_if(&Token::Semicolon);
    }

    /// Try to get a type annotation that ends before the given span and matches the name
    fn try_get_type_annotation(&mut self, before_span: Span, name: &str) -> Option<TypeAnnotation> {
        // Look for a type annotation that ends before this position and matches the name
        while self.annotation_pos < self.type_annotations.len() {
            let ann = &self.type_annotations[self.annotation_pos];
            if ann.span.end <= before_span.start {
                if ann.name == name {
                    self.annotation_pos += 1;
                    return Some(TypeAnnotation {
                        name: ann.name.clone(),
                        content: ann.content.clone(),
                        span: ann.span,
                    });
                }
                // Skip annotations that don't match
                self.annotation_pos += 1;
                continue;
            }
            break;
        }
        None
    }

    /// Try to get a type annotation that matches the name
    /// This is used for functions where the annotation appears before the function declaration
    fn try_get_type_annotation_for_function(&mut self, before_span: Span, name: &str) -> Option<TypeAnnotation> {
        // Look for a type annotation that ends before this position and matches the name
        while self.annotation_pos < self.type_annotations.len() {
            let ann = &self.type_annotations[self.annotation_pos];
            if ann.span.end <= before_span.start {
                if ann.name == name {
                    self.annotation_pos += 1;
                    return Some(TypeAnnotation {
                        name: ann.name.clone(),
                        content: ann.content.clone(),
                        span: ann.span,
                    });
                }
                // Skip annotations that don't match
                self.annotation_pos += 1;
                continue;
            }
            break;
        }
        None
    }
}

/// Parse source code into an AST
pub fn parse(source: &str) -> Result<Program> {
    use crate::lexer::Scanner;

    let scanner = Scanner::new(source);
    let (tokens, type_annotations) = scanner.tokenize()?;

    let mut parser = Parser::new(tokens, type_annotations);
    parser.parse_program()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expr(source: &str) -> Expr {
        let program = parse(source).unwrap();
        match &program.statements[0] {
            Stmt::Expr { expression, .. } => expression.clone(),
            _ => panic!("Expected expression statement"),
        }
    }

    #[test]
    fn test_literals() {
        assert!(matches!(
            parse_expr("42"),
            Expr::Lit { value: Literal::Number(n), .. } if n == 42.0
        ));
        assert!(matches!(
            parse_expr("\"hello\""),
            Expr::Lit { value: Literal::String(s), .. } if s == "hello"
        ));
        assert!(matches!(
            parse_expr("true"),
            Expr::Lit {
                value: Literal::Boolean(true),
                ..
            }
        ));
    }

    #[test]
    fn test_binary_ops() {
        assert!(matches!(
            parse_expr("1 + 2"),
            Expr::Binary { op: BinOp::Add, .. }
        ));
        assert!(matches!(
            parse_expr("a && b"),
            Expr::Binary { op: BinOp::And, .. }
        ));
    }

    #[test]
    fn test_function_call() {
        assert!(matches!(parse_expr("foo()"), Expr::Call { .. }));
        assert!(matches!(parse_expr("foo(1, 2)"), Expr::Call { .. }));
    }

    #[test]
    fn test_member_access() {
        assert!(matches!(parse_expr("a.b"), Expr::Member { .. }));
        assert!(matches!(parse_expr("a[0]"), Expr::ComputedMember { .. }));
    }

    #[test]
    fn test_var_declaration() {
        let program = parse("var x = 1;").unwrap();
        assert!(matches!(&program.statements[0], Stmt::Var { .. }));
    }

    #[test]
    fn test_function_declaration() {
        let program = parse("function foo(a, b) { return a + b; }").unwrap();
        assert!(matches!(&program.statements[0], Stmt::FunctionDecl { .. }));
    }

    #[test]
    fn test_exponentiation_operator() {
        // Test ** operator
        assert!(matches!(
            parse_expr("2 ** 3"),
            Expr::Binary { op: BinOp::Pow, .. }
        ));

        // Test **= operator
        let program = parse("x **= 2;").unwrap();
        assert!(matches!(
            &program.statements[0],
            Stmt::Expr {
                expression: Expr::Assign {
                    op: AssignOp::PowAssign,
                    ..
                },
                ..
            }
        ));
    }

    #[test]
    fn test_regex_literals() {
        // Test simple regex
        assert!(matches!(
            parse_expr("/hello/"),
            Expr::Lit { value: Literal::Regex { pattern, flags }, .. }
            if pattern == "hello" && flags == ""
        ));

        // Test regex with flags
        assert!(matches!(
            parse_expr("/[a-z]+/gi"),
            Expr::Lit { value: Literal::Regex { pattern, flags }, .. }
            if pattern == "[a-z]+" && flags == "gi"
        ));
    }

    #[test]
    fn test_unicode_identifiers() {
        // Test unicode variable names
        let program = parse("var café = 1;").unwrap();
        if let Stmt::Var { declarations, .. } = &program.statements[0] {
            assert_eq!(declarations[0].name, "café");
        } else {
            panic!("Expected var declaration");
        }

        // Test unicode identifier in expression
        assert!(matches!(
            parse_expr("π"),
            Expr::Ident { name, .. } if name == "π"
        ));
    }

    #[test]
    fn test_for_in_loop() {
        // Test for...in with variable declaration
        let program = parse("for (var key in obj) {}").unwrap();
        assert!(matches!(&program.statements[0], Stmt::ForIn { .. }));

        // Test for...in with existing variable
        let program = parse("var k; for (k in obj) {}").unwrap();
        assert!(matches!(&program.statements[1], Stmt::ForIn { .. }));

        // Test that 'in' in for-loop init doesn't get parsed as binary operator
        let program = parse("for (i in obj) {}").unwrap();
        assert!(matches!(&program.statements[0], Stmt::ForIn { .. }));
    }

    #[test]
    fn test_keywords_as_property_names() {
        // Test keywords as object property keys (wrap in parens to avoid ambiguity with block)
        let expr = parse_expr("({if: 1, else: 2, for: 3})");
        if let Expr::Object { properties, .. } = expr {
            assert_eq!(properties.len(), 3);
            // Check that we parsed 'if', 'else', 'for' as property keys
            if let PropDef::Property {
                key: PropKey::Ident(name),
                ..
            } = &properties[0]
            {
                assert_eq!(name, "if");
            } else {
                panic!("Expected property with 'if' key");
            }
        } else {
            panic!("Expected object literal");
        }

        // Test keywords in member access
        assert!(matches!(
            parse_expr("obj.if"),
            Expr::Member { property, .. } if property == "if"
        ));

        assert!(matches!(
            parse_expr("obj.else"),
            Expr::Member { property, .. } if property == "else"
        ));
    }

    #[test]
    fn test_get_set_methods_vs_accessors() {
        // Test methods named 'get' and 'set' (not accessors)
        let expr = parse_expr("({get() { return 1; }, set() { return 2; }})");
        if let Expr::Object { properties, .. } = expr {
            assert_eq!(properties.len(), 2);
            assert!(
                matches!(&properties[0], PropDef::Method { key: PropKey::Ident(name), .. } if name == "get")
            );
            assert!(
                matches!(&properties[1], PropDef::Method { key: PropKey::Ident(name), .. } if name == "set")
            );
        } else {
            panic!("Expected object with method properties");
        }

        // Test actual getter/setter syntax
        let expr = parse_expr("({get prop() { return 1; }, set prop(v) { }})");
        if let Expr::Object { properties, .. } = expr {
            assert_eq!(properties.len(), 2);
            assert!(
                matches!(&properties[0], PropDef::Getter { key: PropKey::Ident(name), .. } if name == "prop")
            );
            assert!(
                matches!(&properties[1], PropDef::Setter { key: PropKey::Ident(name), .. } if name == "prop")
            );
        } else {
            panic!("Expected object with getter/setter");
        }
    }

    #[test]
    fn test_template_literal_no_substitution() {
        let expr = parse_expr("`hello world`");
        assert!(matches!(
            expr,
            Expr::TemplateLiteral { quasis, expressions, .. }
            if quasis == vec!["hello world".to_string()] && expressions.is_empty()
        ));
    }

    #[test]
    fn test_template_literal_with_substitution() {
        let expr = parse_expr("`hello ${name}!`");
        if let Expr::TemplateLiteral {
            quasis,
            expressions,
            ..
        } = expr
        {
            assert_eq!(quasis, vec!["hello ".to_string(), "!".to_string()]);
            assert_eq!(expressions.len(), 1);
            assert!(matches!(&expressions[0], Expr::Ident { name, .. } if name == "name"));
        } else {
            panic!("Expected template literal");
        }
    }

    #[test]
    fn test_template_literal_multiple_substitutions() {
        let expr = parse_expr("`${a} + ${b} = ${c}`");
        if let Expr::TemplateLiteral {
            quasis,
            expressions,
            ..
        } = expr
        {
            assert_eq!(
                quasis,
                vec![
                    "".to_string(),
                    " + ".to_string(),
                    " = ".to_string(),
                    "".to_string()
                ]
            );
            assert_eq!(expressions.len(), 3);
        } else {
            panic!("Expected template literal");
        }
    }

    #[test]
    fn test_template_literal_complex_expression() {
        let expr = parse_expr("`result: ${1 + 2}`");
        if let Expr::TemplateLiteral {
            quasis,
            expressions,
            ..
        } = expr
        {
            assert_eq!(quasis, vec!["result: ".to_string(), "".to_string()]);
            assert_eq!(expressions.len(), 1);
            assert!(matches!(
                &expressions[0],
                Expr::Binary { op: BinOp::Add, .. }
            ));
        } else {
            panic!("Expected template literal");
        }
    }

    #[test]
    fn test_import_default() {
        let program = parse("import foo from 'module';").unwrap();
        if let Stmt::Import {
            specifiers, source, ..
        } = &program.statements[0]
        {
            assert_eq!(source, "module");
            assert_eq!(specifiers.len(), 1);
            assert!(
                matches!(&specifiers[0], ImportSpecifier::Default { local, .. } if local == "foo")
            );
        } else {
            panic!("Expected import statement");
        }
    }

    #[test]
    fn test_import_named() {
        let program = parse("import { foo, bar as baz } from 'module';").unwrap();
        if let Stmt::Import {
            specifiers, source, ..
        } = &program.statements[0]
        {
            assert_eq!(source, "module");
            assert_eq!(specifiers.len(), 2);
            assert!(
                matches!(&specifiers[0], ImportSpecifier::Named { imported, local, .. } if imported == "foo" && local == "foo")
            );
            assert!(
                matches!(&specifiers[1], ImportSpecifier::Named { imported, local, .. } if imported == "bar" && local == "baz")
            );
        } else {
            panic!("Expected import statement");
        }
    }

    #[test]
    fn test_import_default_and_named() {
        let program = parse("import init, { check_types } from './pkg/minfern.js';").unwrap();
        if let Stmt::Import {
            specifiers, source, ..
        } = &program.statements[0]
        {
            assert_eq!(source, "./pkg/minfern.js");
            assert_eq!(specifiers.len(), 2);
            assert!(
                matches!(&specifiers[0], ImportSpecifier::Default { local, .. } if local == "init")
            );
            assert!(
                matches!(&specifiers[1], ImportSpecifier::Named { imported, local, .. } if imported == "check_types" && local == "check_types")
            );
        } else {
            panic!("Expected import statement");
        }
    }

    #[test]
    fn test_import_namespace() {
        let program = parse("import * as utils from 'utils';").unwrap();
        if let Stmt::Import {
            specifiers, source, ..
        } = &program.statements[0]
        {
            assert_eq!(source, "utils");
            assert_eq!(specifiers.len(), 1);
            assert!(
                matches!(&specifiers[0], ImportSpecifier::Namespace { local, .. } if local == "utils")
            );
        } else {
            panic!("Expected import statement");
        }
    }

    #[test]
    fn test_import_side_effect() {
        let program = parse("import 'polyfill';").unwrap();
        if let Stmt::Import {
            specifiers, source, ..
        } = &program.statements[0]
        {
            assert_eq!(source, "polyfill");
            assert!(specifiers.is_empty());
        } else {
            panic!("Expected import statement");
        }
    }
}
