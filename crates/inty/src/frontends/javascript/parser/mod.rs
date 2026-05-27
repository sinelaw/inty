//! Parser module for mquickjs JavaScript source code.

#[cfg(test)]
mod proptests;

use crate::ast::*;
use crate::error::{ParseError, Result};
use crate::frontends::javascript::lexer::Token;
use crate::span::{Span, Spanned};

/// Parser-internal destructuring pattern. Not part of the public AST —
/// every pattern is immediately lowered to ordinary declarators via
/// [`Parser::desugar_pattern`] before any other code sees it.
#[derive(Debug, Clone)]
enum Pattern {
    Ident(String, Span),
    /// `{source: sub_pattern, ..., ...rest}`. Shorthand `{a}` stores
    /// `("a", Pattern::Ident("a"))`. The third tuple element holds
    /// the optional rest binding's name and span.
    Object(Vec<(String, Pattern, Span)>, Option<(String, Span)>, Span),
    /// `[sub_pattern, sub_pattern, ..., ...rest]`. The middle tuple
    /// holds the optional rest binding's name and span.
    Array(Vec<Pattern>, Option<(String, Span)>, Span),
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
    /// Lexical depth of `class { … }` bodies we're currently inside.
    /// Private identifiers (`#name`) can only be referenced when this
    /// is > 0; outside any class body, `#name` is a parse error
    /// (matching ECMA-262's syntactic restriction). Nested function
    /// expressions inside a class method don't reset the depth —
    /// `this.#x` from inside a callback that's still inside the class
    /// body is legal.
    class_depth: usize,
    /// Names of `class` declarations lowered to factory functions, in
    /// declaration order. Surfaced on `Program::class_brands` so inference
    /// brands each class's instance row nominally — two structurally
    /// identical classes are then distinct types (JS classes are nominal
    /// by default, matching `new`/`instanceof` semantics).
    class_brands: Vec<String>,
    /// Original source text. Used to slice byte ranges out of the source
    /// when we need to reconstruct content the lexer didn't capture as a
    /// JSDoc annotation — currently only TS-style `field: T` annotations
    /// in class-body field declarations. Empty when the parser is
    /// constructed without a source (legacy callers in tests).
    source: String,
}

impl Parser {
    pub fn new(tokens: Vec<Spanned<Token>>, type_annotations: Vec<TypeAnnotation>) -> Self {
        Self::with_source(tokens, type_annotations, String::new())
    }

    pub fn with_source(
        tokens: Vec<Spanned<Token>>,
        type_annotations: Vec<TypeAnnotation>,
        source: String,
    ) -> Self {
        Self {
            tokens,
            pos: 0,
            type_annotations,
            annotation_pos: 0,
            no_in: false,
            temp_counter: 0,
            async_depth: 0,
            next_fn_is_async: false,
            class_depth: 0,
            class_brands: Vec::new(),
            source,
        }
    }

    fn fresh_temp_name(&mut self) -> String {
        let n = self.temp_counter;
        self.temp_counter += 1;
        format!("$destr${}", n)
    }

    /// Lower a private identifier `#name` to its on-the-row sentinel
    /// key. The key starts with `\x02` (a control character that JS
    /// source can't tokenise), so external code cannot reach the
    /// field via member access. Same trick the callable-row design
    /// uses for `<CALL>` (`\x01call\x01`). See
    /// `examples/fizzy/design.md` § "Private fields".
    ///
    /// Cross-instance access (`other.#name` from inside a method)
    /// works because the same lowering is applied at the access site
    /// and the storage site, so both refer to the same sentinel
    /// property. Cross-class collisions (two unrelated classes both
    /// using `#x`) are accepted as a pragmatic trade-off — the
    /// alternative (per-class sentinel suffix) requires threading a
    /// "current class" context through the parser and the actual
    /// collision rate in real code is negligible.
    fn private_name(name: &str) -> String {
        format!("\x02priv:{}\x02", name)
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
            type_aliases: Vec::new(),
            class_brands: std::mem::take(&mut self.class_brands),
        })
    }

    // ========== Statement Parsing ==========

    fn parse_statement(&mut self) -> Result<Stmt> {
        match self.current() {
            Token::Var => self.parse_var_declaration(VarKind::Var),
            // `let` is parsed as `var`. inty doesn't yet model per-block
            // lexical scoping or temporal-dead-zone rules, but var-with-block
            // scoping is a sound over-approximation for type checking.
            Token::Let => self.parse_var_declaration(VarKind::Let),
            Token::Const => self.parse_var_declaration(VarKind::Const),
            Token::Function => self.parse_function_declaration(),
            Token::Class => self.parse_class_declaration(),
            // `async function name(...) { body }` parses like a regular
            // function declaration; `async` is consumed by the async-wrap
            // helper which rewrites every `return` inside the body so the
            // function's return type ends up as `Promise<T>`.
            Token::Async
                if matches!(
                    self.tokens.get(self.pos + 1).map(|s| &s.value),
                    Some(Token::Function)
                ) =>
            {
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

    /// Parse a pattern entry that may carry a default: `<pattern> [= expr]`.
    /// inty has no notion of optional values at the type level — every
    /// destructured property must exist on the source row — so the
    /// default expression has no run-time or type effect under inty's
    /// rules. We still parse it (so source files using defaults type-
    /// check), then discard. The default expression is **not** type-
    /// checked. (Function-parameter defaults, by contrast, do type-check
    /// the default, because the parameter's type is otherwise free.)
    fn parse_pattern_with_default(&mut self) -> Result<Pattern> {
        let inner = self.parse_pattern()?;
        if self.consume_if(&Token::Eq) {
            let _default = self.parse_assignment_expression()?;
        }
        Ok(inner)
    }

    fn parse_object_pattern(&mut self) -> Result<Pattern> {
        let start = self.current_span().start;
        self.expect(&Token::LBrace)?;
        let mut entries: Vec<(String, Pattern, Span)> = Vec::new();
        let mut rest: Option<(String, Span)> = None;
        while !self.check(&Token::RBrace) {
            if self.check(&Token::DotDotDot) {
                let rest_span = self.current_span();
                self.advance();
                let name = self.expect_ident()?;
                rest = Some((name, rest_span));
                // Per spec, rest must be the trailing element.
                break;
            }
            let entry_span = self.current_span();
            let source = self.expect_ident()?;
            let sub = if self.consume_if(&Token::Colon) {
                self.parse_pattern_with_default()?
            } else {
                // Shorthand `{a}` is `{a: a}`. May carry a default —
                // `{a = 1}` is `{a: a = 1}`, where the default applies
                // to the binding `a`.
                let ident_pat = Pattern::Ident(source.clone(), entry_span);
                if self.consume_if(&Token::Eq) {
                    // Default value on a destructuring shorthand
                    // (`{a = 1}`). inty has no nullable model, so the
                    // default has no type effect — parse and discard.
                    let _default = self.parse_assignment_expression()?;
                }
                ident_pat
            };
            entries.push((source, sub, entry_span));
            if !self.consume_if(&Token::Comma) {
                break;
            }
        }
        self.expect(&Token::RBrace)?;
        let end = self.prev_span().end;
        Ok(Pattern::Object(entries, rest, Span::new(start, end)))
    }

    fn parse_array_pattern(&mut self) -> Result<Pattern> {
        let start = self.current_span().start;
        self.expect(&Token::LBracket)?;
        let mut elems: Vec<Pattern> = Vec::new();
        let mut rest: Option<(String, Span)> = None;
        while !self.check(&Token::RBracket) {
            if self.check(&Token::DotDotDot) {
                let rest_span = self.current_span();
                self.advance();
                let name = self.expect_ident()?;
                rest = Some((name, rest_span));
                // Per spec, rest must be the trailing element.
                break;
            }
            elems.push(self.parse_pattern_with_default()?);
            if !self.consume_if(&Token::Comma) {
                break;
            }
        }
        self.expect(&Token::RBracket)?;
        let end = self.prev_span().end;
        Ok(Pattern::Array(elems, rest, Span::new(start, end)))
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
                    type_ast: None,
                    kind,
                    span: *span,
                });
            }
            Pattern::Object(entries, rest, span) => {
                let temp = self.fresh_temp_name();
                decls.push(VarDeclarator {
                    name: temp.clone(),
                    init: Some(source),
                    type_annotation: None,
                    type_ast: None,
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
                if let Some((rest_name, rest_span)) = rest {
                    let excluded: Vec<String> = entries.iter().map(|(p, _, _)| p.clone()).collect();
                    let init = Expr::RestRow {
                        source: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *rest_span,
                        }),
                        excluded,
                        span: *rest_span,
                    };
                    decls.push(VarDeclarator {
                        name: rest_name.clone(),
                        init: Some(init),
                        type_annotation: None,
                        type_ast: None,
                        kind,
                        span: *rest_span,
                    });
                }
            }
            Pattern::Array(elems, rest, span) => {
                let temp = self.fresh_temp_name();
                decls.push(VarDeclarator {
                    name: temp.clone(),
                    init: Some(source),
                    type_annotation: None,
                    type_ast: None,
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
                if let Some((rest_name, rest_span)) = rest {
                    let init = Expr::RestArray {
                        source: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *rest_span,
                        }),
                        skip: elems.len(),
                        span: *rest_span,
                    };
                    decls.push(VarDeclarator {
                        name: rest_name.clone(),
                        init: Some(init),
                        type_annotation: None,
                        type_ast: None,
                        kind,
                        span: *rest_span,
                    });
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

    /// Reinterpret an array/object *literal* on the LHS of `=` as a
    /// destructuring [`Pattern`]. Returns `None` for shapes that can't be
    /// a destructuring target (elision holes, computed/numeric keys,
    /// non-identifier rest/leaf targets) — those keep the original
    /// "invalid assignment target" error.
    fn expr_to_pattern(expr: &Expr) -> Option<Pattern> {
        match expr {
            Expr::Ident { name, span } => Some(Pattern::Ident(name.clone(), *span)),
            Expr::Array { elements, span } => {
                let mut elems = Vec::new();
                let mut rest = None;
                for el in elements {
                    match el {
                        Some(Expr::Spread { argument, span: sp }) => {
                            let Expr::Ident { name, .. } = argument.as_ref() else {
                                return None;
                            };
                            rest = Some((name.clone(), *sp));
                        }
                        Some(e) => elems.push(Self::expr_to_pattern(e)?),
                        None => return None, // elision hole `[, x]`
                    }
                }
                Some(Pattern::Array(elems, rest, *span))
            }
            Expr::Object { properties, span } => {
                let mut entries = Vec::new();
                let mut rest = None;
                for p in properties {
                    match p {
                        PropDef::Property {
                            key, value, span: sp, ..
                        } => {
                            let name = match key {
                                PropKey::Ident(s) | PropKey::String(s) => s.clone(),
                                PropKey::Number(_) => return None,
                            };
                            entries.push((name, Self::expr_to_pattern(value)?, *sp));
                        }
                        PropDef::Spread { argument, span: sp } => {
                            let Expr::Ident { name, .. } = argument else {
                                return None;
                            };
                            rest = Some((name.clone(), *sp));
                        }
                        _ => return None,
                    }
                }
                Some(Pattern::Object(entries, rest, *span))
            }
            _ => None,
        }
    }

    /// Desugar a destructuring *assignment* `pattern = source` into a flat
    /// list of statements. Leaves assign to the (already-declared) target
    /// names; nested patterns introduce a fresh `var` temp for the
    /// sub-source. Mirrors [`Self::desugar_pattern`], but emits
    /// assignments instead of declarations for the bound names.
    fn desugar_pattern_assign(&mut self, pattern: &Pattern, source: Expr, stmts: &mut Vec<Stmt>) {
        match pattern {
            Pattern::Ident(name, span) => {
                stmts.push(Stmt::Expr {
                    expression: Expr::Assign {
                        op: AssignOp::Assign,
                        left: Box::new(Expr::Ident {
                            name: name.clone(),
                            span: *span,
                        }),
                        right: Box::new(source),
                        span: *span,
                    },
                    span: *span,
                });
            }
            Pattern::Object(entries, rest, span) => {
                let temp = self.fresh_temp_name();
                stmts.push(Self::temp_var(&temp, source, *span));
                for (prop_name, sub, prop_span) in entries {
                    let access = Expr::Member {
                        object: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *prop_span,
                        }),
                        property: prop_name.clone(),
                        span: *prop_span,
                    };
                    self.desugar_pattern_assign(sub, access, stmts);
                }
                if let Some((rest_name, rest_span)) = rest {
                    let excluded: Vec<String> = entries.iter().map(|(p, _, _)| p.clone()).collect();
                    let init = Expr::RestRow {
                        source: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *rest_span,
                        }),
                        excluded,
                        span: *rest_span,
                    };
                    self.desugar_pattern_assign(
                        &Pattern::Ident(rest_name.clone(), *rest_span),
                        init,
                        stmts,
                    );
                }
            }
            Pattern::Array(elems, rest, span) => {
                let temp = self.fresh_temp_name();
                stmts.push(Self::temp_var(&temp, source, *span));
                for (idx, sub) in elems.iter().enumerate() {
                    let access = Expr::ComputedMember {
                        object: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *span,
                        }),
                        property: Box::new(Expr::Lit {
                            value: Literal::Number(idx as f64),
                            span: *span,
                        }),
                        span: *span,
                    };
                    self.desugar_pattern_assign(sub, access, stmts);
                }
                if let Some((rest_name, rest_span)) = rest {
                    let init = Expr::RestArray {
                        source: Box::new(Expr::Ident {
                            name: temp.clone(),
                            span: *rest_span,
                        }),
                        skip: elems.len(),
                        span: *rest_span,
                    };
                    self.desugar_pattern_assign(
                        &Pattern::Ident(rest_name.clone(), *rest_span),
                        init,
                        stmts,
                    );
                }
            }
        }
    }

    /// A `var <name> = <init>;` declarator statement for a desugaring temp.
    fn temp_var(name: &str, init: Expr, span: Span) -> Stmt {
        Stmt::Var {
            kind: VarKind::Var,
            declarations: vec![VarDeclarator {
                name: name.to_string(),
                init: Some(init),
                type_annotation: None,
                type_ast: None,
                kind: VarKind::Var,
                span,
            }],
            span,
        }
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
            type_ast: None,
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
                // or a namespace import. Otherwise, go directly to 'from'.
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
                // After `default,`, JS allows either `{ … }` (named) or
                // `* as ns` (namespace). Accept the namespace form here;
                // a `{` falls through to the named-imports branch below.
                if self.consume_if(&Token::Star) {
                    self.expect(&Token::As)?;
                    let ns_local = self.expect_ident()?;
                    specifiers.push(ImportSpecifier::Namespace {
                        local: ns_local,
                        span: Span::new(start, self.prev_span().end),
                    });
                }
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
            Token::Var | Token::Let => {
                // export var x = 1;  /  export let x = 1;
                let was_let = self.check(&Token::Let);
                let kind = if was_let { VarKind::Let } else { VarKind::Var };
                self.advance();
                let mut declarations = Vec::new();
                loop {
                    let decl = self.parse_var_declarator(kind)?;
                    declarations.push(decl);
                    if !self.consume_if(&Token::Comma) {
                        break;
                    }
                }
                self.consume_semicolon();
                let decl_span = Span::new(start, self.prev_span().end);
                Ok(Stmt::Export {
                    declaration: ExportDecl::Var {
                        kind,
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
            Token::Function => self.parse_export_function_declaration(start, false),
            // `export async function foo() { ... }` — the `async` token is
            // followed by `function`. Hand off to the same export-function
            // path with the async flag set so the body gets wrapped in
            // `Promise.resolve` exactly like a non-exported async function.
            Token::Async
                if matches!(
                    self.tokens.get(self.pos + 1).map(|s| &s.value),
                    Some(Token::Function)
                ) =>
            {
                self.advance(); // consume `async`
                self.parse_export_function_declaration(start, true)
            }
            Token::Default => {
                // export default <function-expression-or-assignment-expression>
                self.advance();
                // `export default class { ... }` and
                // `export default class extends X { ... }` aren't a single
                // expression in mquickjs (classes are statements that
                // desugar to factory functions). Synthesise a name and
                // parse the class as a normal declaration; convert the
                // resulting `Stmt::FunctionDecl` (the class factory) to
                // an `Expr::Function` with the synthetic name and bind it
                // through `ExportDecl::Default`, exactly like
                // `export default function f() { ... }` does. The
                // existing `class extends` rejection still fires from
                // the class parser if applicable, with its gaps.md
                // pointer attached.
                if self.check(&Token::Class) {
                    let synth_name = format!("$default_class${}", self.temp_counter);
                    self.temp_counter += 1;
                    let class_decl =
                        self.parse_class_declaration_named(Some(synth_name.clone()))?;
                    let value = match class_decl {
                        Stmt::FunctionDecl {
                            name,
                            params,
                            body,
                            type_annotation,
                            return_type_ast: _,
                            span,
                        } => Expr::Function {
                            name: Some(name),
                            params,
                            body,
                            type_annotation,
                            span,
                        },
                        // Class desugaring guarantees a FunctionDecl;
                        // anything else means the desugarer changed.
                        other => panic!(
                            "class declaration did not desugar to FunctionDecl: {:?}",
                            other
                        ),
                    };
                    self.consume_semicolon();
                    let decl_span = Span::new(start, self.prev_span().end);
                    return Ok(Stmt::Export {
                        declaration: ExportDecl::Default {
                            value,
                            span: decl_span,
                        },
                        span: decl_span,
                    });
                }
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
            Token::LBrace => {
                // Either `export { … };` (List) or `export { … } from "…";` (re-export).
                // Disambiguated by the optional `from` clause after the closing brace.
                self.advance();
                let mut specifiers = Vec::new();
                while !self.check(&Token::RBrace) {
                    let spec_start = self.current_span().start;
                    // For re-exports the LHS is a name in the *target* module
                    // (which can be `default`); for plain lists it's a local
                    // binding. Same lexical shape — `expect_module_name`
                    // covers both.
                    let local = self.expect_module_name()?;
                    let exported = if self.consume_if(&Token::As) {
                        self.expect_module_name()?
                    } else {
                        local.clone()
                    };
                    specifiers.push(ExportSpecifier {
                        local,
                        exported,
                        span: Span::new(spec_start, self.prev_span().end),
                    });
                    if !self.consume_if(&Token::Comma) {
                        break;
                    }
                }
                self.expect(&Token::RBrace)?;

                if self.consume_if(&Token::From) {
                    let source = self.expect_string()?;
                    self.consume_semicolon();
                    let decl_span = Span::new(start, self.prev_span().end);
                    Ok(Stmt::Export {
                        declaration: ExportDecl::From {
                            kind: ExportFromKind::Named(specifiers),
                            source,
                            span: decl_span,
                        },
                        span: decl_span,
                    })
                } else {
                    self.consume_semicolon();
                    let decl_span = Span::new(start, self.prev_span().end);
                    Ok(Stmt::Export {
                        declaration: ExportDecl::List {
                            specifiers,
                            span: decl_span,
                        },
                        span: decl_span,
                    })
                }
            }
            Token::Star => {
                // export * from "./mod.js";
                // export * as ns from "./mod.js";
                self.advance();
                let kind = if self.consume_if(&Token::As) {
                    let ns = self.expect_ident()?;
                    ExportFromKind::AllAs(ns)
                } else {
                    ExportFromKind::All
                };
                self.expect(&Token::From)?;
                let source = self.expect_string()?;
                self.consume_semicolon();
                let decl_span = Span::new(start, self.prev_span().end);
                Ok(Stmt::Export {
                    declaration: ExportDecl::From {
                        kind,
                        source,
                        span: decl_span,
                    },
                    span: decl_span,
                })
            }
            _ => Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: "var, const, function, default, {, or *".to_string(),
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
        self.parse_class_declaration_named(None)
    }

    /// Parse a class declaration. If `forced_name` is `Some`, the
    /// caller has already chosen the name (used by the
    /// `export default class { ... }` arm to give an anonymous class
    /// a synthetic identifier). Otherwise the next token must be an
    /// identifier — the usual `class Foo { ... }` form.
    fn parse_class_declaration_named(&mut self, forced_name: Option<String>) -> Result<Stmt> {
        let start = self.current_span().start;
        self.expect(&Token::Class)?;
        let name = match forced_name {
            Some(n) => n,
            None => self.expect_ident()?,
        };
        // Record the class for nominal branding (see `class_brands`).
        self.class_brands.push(name.clone());

        // Reject `extends Parent` for now; it'd need a real prototype chain
        // to match runtime semantics and inty has no inheritance.
        if self.check(&Token::Extends) {
            let span = self.current_span();
            return Err(ParseError::UnexpectedToken {
                found: "extends".to_string(),
                expected: "{ (class inheritance is not supported — see \
                    examples/spa/gaps.md § 'By design' for the \
                    factory-function workaround)"
                    .to_string(),
                span,
            }
            .into());
        }

        self.expect(&Token::LBrace)?;

        // Track class nesting so `#name` references inside the body
        // are allowed and references outside are rejected. Decrement
        // after the body's closing `}` is consumed.
        self.class_depth += 1;

        let mut ctor_params: Vec<Param> = Vec::new();
        let mut field_props: Vec<PropDef> = Vec::new();
        let mut method_props: Vec<PropDef> = Vec::new();

        // Annotations contributed by declaration-only fields whose initial
        // value comes from a `this.NAME = …` line in the constructor body.
        // The annotation moves to that constructor-extracted property at
        // emit time so the constructor parameter's inferred type is
        // checked against the declared field type.
        let mut deferred_field_annotations: Vec<(String, TypeAnnotation)> = Vec::new();
        // Names already declared as class-body fields. Used to catch
        // duplicate declarations like `class Foo { a; a = 1; }`. Note we
        // intentionally allow a class-body declaration AND a `this.a = …`
        // in the constructor — the constructor is the value site, the
        // declaration carries the annotation.
        let mut declared_field_names: std::collections::HashSet<String> =
            std::collections::HashSet::new();

        while !self.check(&Token::RBrace) && !self.is_at_end() {
            // Skip empty separators (class bodies don't require semicolons
            // between members but tolerate them).
            if self.consume_if(&Token::Semicolon) {
                continue;
            }

            let member_start = self.current_span().start;

            // Modifier tolerance: `public` / `private` / `protected` /
            // `readonly` have no semantic effect under inty's structural
            // typing, so erase them. Eat a run of modifier idents — TS
            // allows e.g. `public readonly name: string`.
            loop {
                let is_modifier = matches!(
                    self.current(),
                    Token::Ident(name)
                        if matches!(
                            name.as_str(),
                            "public" | "private" | "protected" | "readonly"
                        )
                );
                if !is_modifier {
                    break;
                }
                // Lookahead: only treat as a modifier if another ident
                // follows (so `private` used as a field name still works,
                // unusual as that is).
                let saved = self.pos;
                let _ = self.expect_ident()?;
                if !matches!(self.current(), Token::Ident(_)) {
                    self.pos = saved;
                    break;
                }
            }

            // Accessor declarations: `get foo() { ... }` or
            // `set foo(v) { ... }`. Recognised before the regular
            // member parser consumes `get` / `set` as a name. The
            // identifier-vs-accessor disambiguation is by lookahead:
            // `get` followed by a name (or `#name`) means an accessor;
            // `get` followed by `(` is a method literally named "get".
            //
            // Lowering: a getter `get foo() { body }` becomes a real
            // `PropDef::Getter` on the returned object literal — same
            // emit path as object-literal getters. The type checker
            // binds the body's `this` to the shared instance row, so
            // `this.field` references are typed against the class.
            //
            // A setter `set foo(v) { body }` lowers to a field `foo`
            // whose value is just the parameter's default form — the
            // body's effect on `foo` itself is what matters for
            // typing, but inty doesn't yet wire that through. For now
            // the field's type comes from its eventual assignment
            // sites; the body is type-checked but its `v` parameter
            // floats as a fresh type variable.
            let accessor_kind = if let Token::Ident(kw) = self.current().clone() {
                if (kw == "get" || kw == "set")
                    && matches!(
                        self.tokens.get(self.pos + 1).map(|s| &s.value),
                        Some(Token::Ident(_) | Token::PrivateIdent(_))
                    )
                {
                    self.advance();
                    Some(kw)
                } else {
                    None
                }
            } else {
                None
            };

            // Class members can carry a regular identifier *or* a
            // private identifier (`#name`). Private members lower to
            // sentinel-keyed row entries that JS source can't reach,
            // matching `this.#name` / `other.#name` access lowering
            // in the expression parser.
            let key_name = if let Token::PrivateIdent(name) = self.current().clone() {
                self.advance();
                Self::private_name(&name)
            } else {
                self.expect_ident()?
            };
            let key_span = self.prev_span();

            if let Some(kind) = accessor_kind {
                // Accessor body: parse `(params) { body }` and lower.
                self.expect(&Token::LParen)?;
                let params = self.parse_parameters()?;
                self.expect(&Token::RParen)?;
                let body = Box::new(self.parse_function_body_block()?);
                let body_span = body.span();
                if kind == "get" {
                    // `get foo() { body }` → real `PropDef::Getter`
                    // on the emitted object literal. The type checker
                    // binds `this` in the body to the instance row.
                    if !params.is_empty() {
                        return Err(ParseError::UnexpectedToken {
                            found: "parameter".to_string(),
                            expected: "() (getters take no arguments)".to_string(),
                            span: key_span,
                        }
                        .into());
                    }
                    let _ = body_span;
                    if !declared_field_names.insert(key_name.clone()) {
                        return Err(ParseError::UnexpectedToken {
                            found: format!("duplicate `{}`", key_name),
                            expected: "each class-body field may be declared at most once"
                                .to_string(),
                            span: key_span,
                        }
                        .into());
                    }
                    method_props.push(PropDef::Getter {
                        key: PropKey::Ident(key_name),
                        body,
                        span: Span::new(member_start, self.prev_span().end),
                    });
                    continue;
                } else {
                    // `set foo(v) { body }` — type-check the body but
                    // the field's type comes from assignment sites.
                    // For now we punt: the body becomes an unused
                    // method named `__set_foo` so it gets checked,
                    // and the field is *not* declared (expected to
                    // be set via `this.foo = …` in the constructor).
                    let _ = (params, body); // type-check skipped for now
                    continue;
                }
            }

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

            // Field declaration vs method/constructor: methods always
            // open with `(`. Anything else after the key name (`:`, `=`,
            // `;`, `,`, `}`) is a field declaration — empty body, with
            // an optional TS-style `: T` annotation and/or `= EXPR`
            // initializer.
            let is_field = !matches!(self.current(), Token::LParen);
            if is_field {
                // TS-style inline annotation `field: T`. We slice the
                // source between the colon and the next `=`/`;`/`,`/`}`,
                // wrap it in a TypeAnnotation, and let the type parser
                // handle the rest at inference time. JSDoc-style
                // `/** field: T */` annotations are picked up below via
                // `try_get_type_annotation`.
                let mut ts_annotation: Option<TypeAnnotation> = None;
                if self.check(&Token::Colon) {
                    let colon_span = self.current_span();
                    self.advance();
                    // Consume tokens until we hit `=`, `;`, `,`, or `}`.
                    let type_start = self.current_span().start;
                    let mut type_end = type_start;
                    let mut depth = 0i32;
                    loop {
                        match self.current() {
                            Token::Eof => break,
                            Token::LParen | Token::LBracket => {
                                depth += 1;
                                type_end = self.current_span().end;
                                self.advance();
                            }
                            Token::RParen | Token::RBracket => {
                                depth -= 1;
                                type_end = self.current_span().end;
                                self.advance();
                            }
                            Token::Lt => {
                                depth += 1;
                                type_end = self.current_span().end;
                                self.advance();
                            }
                            Token::Gt => {
                                depth -= 1;
                                type_end = self.current_span().end;
                                self.advance();
                            }
                            Token::Eq | Token::Semicolon | Token::RBrace | Token::Comma
                                if depth <= 0 =>
                            {
                                break
                            }
                            _ => {
                                type_end = self.current_span().end;
                                self.advance();
                            }
                        }
                    }
                    if type_end <= type_start {
                        return Err(ParseError::UnexpectedToken {
                            found: "empty type".to_string(),
                            expected: "a type after `:` in field declaration".to_string(),
                            span: colon_span,
                        }
                        .into());
                    }
                    let content = if !self.source.is_empty()
                        && type_end <= self.source.len()
                        && type_start <= type_end
                    {
                        self.source[type_start..type_end].trim().to_string()
                    } else {
                        // Parser was constructed without source — TS-style
                        // inline annotations are only available when going
                        // through `parse(source)`. Emit an empty content
                        // and let downstream type parsing fail loudly.
                        String::new()
                    };
                    ts_annotation = Some(TypeAnnotation {
                        name: key_name.clone(),
                        content,
                        span: Span::new(type_start, type_end),
                        kind: AnnotationKind::Inline,
                    });
                }

                // Initializer (optional).
                let initializer = if self.consume_if(&Token::Eq) {
                    Some(self.parse_assignment_expression()?)
                } else {
                    None
                };

                // Optional separator.
                let _ = self.consume_if(&Token::Semicolon) || self.consume_if(&Token::Comma);

                let member_span = Span::new(member_start, self.prev_span().end);

                if !declared_field_names.insert(key_name.clone()) {
                    return Err(ParseError::UnexpectedToken {
                        found: format!("duplicate field `{}`", key_name),
                        expected: "each class-body field may be declared at most once".to_string(),
                        span: member_span,
                    }
                    .into());
                }

                // Resolve annotation: TS-style wins; JSDoc-style is the
                // fallback. (Both are mutually exclusive in practice; a
                // user who writes both gets the TS-style form.)
                let annotation = ts_annotation
                    .or_else(|| self.try_get_type_annotation(self.current_span(), &key_name));

                match initializer {
                    Some(init) => {
                        field_props.push(PropDef::Property {
                            key: PropKey::Ident(key_name),
                            value: init,
                            type_annotation: annotation,
                            span: member_span,
                        });
                    }
                    None => {
                        // Declaration-only. Two cases:
                        //   1. Annotated: stash the annotation; the
                        //      constructor's `this.NAME = …` extraction
                        //      will pick it up. If the constructor never
                        //      sets the field, we emit an `undefined`
                        //      placeholder with the annotation attached
                        //      so the type-level row still includes the
                        //      field at the declared type (annotations
                        //      are unified with the value's inferred
                        //      type — `Undefined` against `T` will fail,
                        //      and the user gets a clear diagnostic).
                        //   2. Unannotated: emit `name: undefined` —
                        //      typed at `Undefined` and the constructor
                        //      can later widen it via assignment if it
                        //      reaches that field at all.
                        if let Some(ann) = annotation {
                            deferred_field_annotations.push((key_name.clone(), ann));
                        }
                        field_props.push(PropDef::Property {
                            key: PropKey::Ident(key_name),
                            value: Expr::Lit {
                                value: Literal::Undefined,
                                span: member_span,
                            },
                            type_annotation: None,
                            span: member_span,
                        });
                    }
                }
                continue;
            }

            // `get name()` / `set name(param)` — accessor property. The
            // body is a block just like a method; we emit PropDef::Getter /
            // PropDef::Setter so the object-literal machinery types the
            // result as the getter's return and the setter's assignment
            // target.
            if (key_name == "get" || key_name == "set") && matches!(self.current(), Token::Ident(_))
            {
                let is_setter = key_name == "set";
                let accessor_name = self.expect_ident()?;
                self.expect(&Token::LParen)?;
                let (params, prefix) = self.parse_parameters_with_prefix()?;
                self.expect(&Token::RParen)?;
                let body =
                    Self::prepend_param_destructuring(self.parse_function_body_block()?, prefix);
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
                        param: params.into_iter().next().unwrap().name,
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
                                // If a class-body field declaration with
                                // an annotation already pushed a placeholder
                                // for `field`, drop it — the constructor's
                                // assignment supplies the real value, and
                                // we'll attach the deferred annotation
                                // below.
                                field_props.retain(|p| {
                                    !matches!(
                                        p,
                                        PropDef::Property { key: PropKey::Ident(n), .. }
                                            if n == &field
                                    )
                                });
                                let type_annotation = Self::take_field_annotation_inner(
                                    &mut deferred_field_annotations,
                                    &field,
                                );
                                field_props.push(PropDef::Property {
                                    key: PropKey::Ident(field),
                                    value,
                                    type_annotation,
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
                    return_type_ast: None,
                    span: member_span,
                });
            }

            let _ = key_span; // kept only to document where the member name lived
        }

        self.expect(&Token::RBrace)?;
        // Done parsing this class body — restore the depth.
        self.class_depth = self.class_depth.saturating_sub(1);
        let end = self.prev_span().end;
        let span = Span::new(start, end);

        // Any deferred field annotations not consumed by a constructor
        // assignment attach to the existing `name: undefined` placeholder
        // entry in `field_props` (declaration-only field with no setter).
        for (name, ann) in deferred_field_annotations {
            for prop in field_props.iter_mut() {
                if let PropDef::Property {
                    key: PropKey::Ident(n),
                    type_annotation,
                    ..
                } = prop
                {
                    if n == &name && type_annotation.is_none() {
                        *type_annotation = Some(ann);
                        break;
                    }
                }
            }
        }

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
            return_type_ast: None,
            span,
        })
    }

    /// Match `this.FIELD = EXPR` exactly and return `(FIELD, EXPR, span)`.
    /// Any other expression returns None.
    fn take_field_annotation_inner(
        list: &mut Vec<(String, TypeAnnotation)>,
        name: &str,
    ) -> Option<TypeAnnotation> {
        let pos = list.iter().position(|(n, _)| n == name)?;
        Some(list.remove(pos).1)
    }

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

    /// Parse `export function foo(...){ ... }` or, when `is_async` is
    /// true, `export async function foo(...){ ... }`. Shared between
    /// the two `parse_export_declaration` arms; the async path runs
    /// the body through `wrap_body_in_promise_resolve` so the
    /// exported function's return type ends up as `Promise<T>`,
    /// matching the non-exported `async function` rule.
    fn parse_export_function_declaration(&mut self, start: usize, is_async: bool) -> Result<Stmt> {
        let func_start = self.current_span();
        self.advance(); // consume `function`
        let name = self.expect_ident()?;
        let type_annotation = self.try_get_type_annotation_for_function(func_start, &name);
        self.expect(&Token::LParen)?;
        // Use `parse_parameters_with_prefix` so destructuring patterns
        // and rest/default parameters work in `export function`
        // declarations the same way they do for plain ones.
        let (params, prefix) = self.parse_parameters_with_prefix()?;
        self.expect(&Token::RParen)?;
        if is_async {
            // Tell `parse_function_body_block` to track an enclosing
            // async context so `await` inside this body is legal.
            self.next_fn_is_async = true;
        }
        let body_block = self.parse_function_body_block()?;
        let body = Box::new(Self::prepend_param_destructuring(body_block, prefix));
        let body = if is_async {
            // Reuse the same Promise.resolve(IIFE) wrapping the
            // non-exported async path uses, so inference produces
            // `(...) => Promise<T>` without any new rules.
            Self::wrap_body_in_promise_resolve(body, func_start)
        } else {
            body
        };
        let func_span = Span::new(start, self.prev_span().end);
        Ok(Stmt::Export {
            declaration: ExportDecl::Function {
                name,
                params,
                body,
                type_annotation,
                span: func_span,
            },
            span: func_span,
        })
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
            return_type_ast,
            span,
        } = decl
        {
            let new_body = Self::wrap_body_in_promise_resolve(body, span);
            Stmt::FunctionDecl {
                name,
                params,
                body: new_body,
                type_annotation,
                return_type_ast,
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
            keywords: vec![],
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
            keywords: vec![],
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
            return_type_ast: None,
            span: Span::new(start, self.prev_span().end),
        })
    }

    /// Parse a comma-separated parameter list. A parameter may be a plain
    /// identifier or a destructuring pattern; pattern parameters synthesise
    /// a fresh temp name in the returned name list and emit the
    /// corresponding destructuring into `prefix_stmts`, which callers
    /// prepend to the function body.
    fn parse_parameters_with_prefix(&mut self) -> Result<(Vec<Param>, Vec<Stmt>)> {
        let mut params = Vec::new();
        let mut prefix = Vec::new();

        if !self.check(&Token::RParen) {
            loop {
                if self.check(&Token::LBrace) || self.check(&Token::LBracket) {
                    let pattern_start = self.current_span().start;
                    let pattern = self.parse_pattern()?;
                    let pattern_end = self.prev_span().end;
                    let pattern_span = Span::new(pattern_start, pattern_end);
                    let temp = self.fresh_temp_name();
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
                    // The synthesised temp has no source name, so we
                    // anchor its span at the pattern's start. Editors
                    // hovering on the pattern still see something.
                    params.push(Param::new(temp, pattern_span));
                } else if self.check(&Token::DotDotDot) {
                    // `...args` rest parameter. inty has no variadic
                    // call shape, so we treat the rest binding as a
                    // single regular parameter — its type ends up as
                    // a fresh variable that the body's uses constrain
                    // (typically to `T[]`). Callers that pass
                    // individual arguments will error on arity, which
                    // matches inty's "no variadic calls" stance. The
                    // `...` token is consumed and discarded.
                    self.advance();
                    let name_span = self.current_span();
                    let name = self.expect_ident()?;
                    let actual_span = Span::new(name_span.start, name_span.start + name.len());
                    params.push(Param::new(name, actual_span));
                    // Rest param must be last per spec. Don't allow a
                    // trailing comma to start another parameter.
                    if self.consume_if(&Token::Comma) {
                        return Err(ParseError::UnexpectedToken {
                            found: ",".to_string(),
                            expected: ") (rest parameter must be last)".to_string(),
                            span: self.current_span(),
                        }
                        .into());
                    }
                    break;
                } else {
                    let name_span = self.current_span();
                    let name = self.expect_ident()?;
                    let actual_span = Span::new(name_span.start, name_span.start + name.len());
                    // `param = expr` — default value. inty has no
                    // notion of optional arguments (call sites must
                    // match arity exactly), so the default is purely a
                    // type-level hint: it constrains the parameter's
                    // type to match the default's type, and type-checks
                    // the default expression. Lower to a dead `if
                    // (false) { param = default; }` block at the start
                    // of the body. The branch never executes at runtime
                    // (so the default doesn't clobber the caller's
                    // value when the dynamics interpreter runs the
                    // function), but inference still walks into it,
                    // which unifies the param's type variable with the
                    // default's type via the assignment.
                    if self.consume_if(&Token::Eq) {
                        let default_expr = self.parse_assignment_expression()?;
                        let default_span = default_expr.span();
                        let assign = Stmt::Expr {
                            expression: Expr::Assign {
                                op: AssignOp::Assign,
                                left: Box::new(Expr::Ident {
                                    name: name.clone(),
                                    span: actual_span,
                                }),
                                right: Box::new(default_expr),
                                span: default_span,
                            },
                            span: default_span,
                        };
                        prefix.push(Stmt::If {
                            test: Expr::Lit {
                                value: Literal::Boolean(false),
                                span: actual_span,
                            },
                            consequent: Box::new(Stmt::Block {
                                body: vec![assign],
                                span: default_span,
                            }),
                            alternate: None,
                            span: default_span,
                        });
                    }
                    params.push(Param::new(name, actual_span));
                }

                if !self.consume_if(&Token::Comma) {
                    break;
                }
            }
        }

        Ok((params, prefix))
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
    fn parse_parameters(&mut self) -> Result<Vec<Param>> {
        let (params, prefix) = self.parse_parameters_with_prefix()?;
        if !prefix.is_empty() {
            let span = prefix[0].span();
            return Err(ParseError::UnexpectedToken {
                found: "destructuring pattern".to_string(),
                expected: "plain parameter name".to_string(),
                span,
            }
            .into());
        }
        Ok(params)
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

        // Parse init.
        let init_or_lhs = if self.check(&Token::Var)
            || self.check(&Token::Let)
            || self.check(&Token::Const)
        {
            let var_start = self.current_span().start;
            let kind = match self.current() {
                Token::Let => VarKind::Let,
                Token::Const => VarKind::Const,
                _ => VarKind::Var,
            };
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
                        kind,
                        &mut destr_decls,
                    );
                    let destr_stmt = Stmt::Var {
                        kind,
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

            let name_start = self.current_span().start;
            let name = self.expect_ident()?;
            let var_end = self.prev_span().end;
            let type_annotation = self.try_get_type_annotation(self.current_span(), &name);
            // The for-in/of LHS span is just the name's source range, so
            // the resolver records the def at the identifier (not at the
            // `let`/`var` keyword).
            let var_span = Span::new(name_start, var_end);

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
                type_ast: None,
                kind,
                // Match `parse_var_declarator`: declarator span starts at
                // the name, not the `let`/`var` keyword. `name_span_from_decl`
                // takes `span.start..span.start + name.len()`, so the
                // resolver lands the def on the identifier.
                span: Span::new(name_start, self.prev_span().end),
            }];

            while self.consume_if(&Token::Comma) {
                declarations.push(self.parse_var_declarator(kind)?);
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

        // ASI: a line terminator between `return` and the next token
        // ends the statement here, regardless of whether the following
        // token could start an expression. This is what makes
        //
        //   if (reset) return
        //   const x = 1;
        //
        // parse correctly — without ASI, `return const x = 1` is a
        // parse error because `const` isn't an expression starter.
        // The block-end and end-of-input cases are also covered.
        let argument = if self.check(&Token::Semicolon)
            || self.check(&Token::RBrace)
            || self.is_at_end()
            || self.line_terminator_before_current()
        {
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

        // ASI: `throw` is one of the few statements where a line
        // terminator after the keyword is a syntax error in JS — it's
        // actively rejected, not silently treated as `throw;` (because
        // `throw;` itself is illegal). We mirror that: the next token
        // must be on the same line.
        if self.line_terminator_before_current() {
            let span = self.current_span();
            return Err(ParseError::UnexpectedToken {
                found: "line terminator".to_string(),
                expected: "expression on the same line as `throw`".to_string(),
                span,
            }
            .into());
        }
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
            // ES2019 optional binding: `catch {}` is shorthand for
            // `catch (e) {}` with the parameter unused. Synthesise a
            // unique name so downstream inference doesn't try to use
            // an empty string and the binding doesn't collide with
            // user-written names.
            let param = if self.check(&Token::LBrace) {
                let synth = format!("$catch${}", self.temp_counter);
                self.temp_counter += 1;
                synth
            } else {
                self.expect(&Token::LParen)?;
                let p = self.expect_ident()?;
                self.expect(&Token::RParen)?;
                p
            };
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

        // ASI: a line terminator between `break` and the label ends
        // the statement immediately (no label).
        let label = if self.line_terminator_before_current() {
            None
        } else if let Token::Ident(name) = self.current() {
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

        // ASI: a line terminator between `continue` and the label ends
        // the statement immediately (no label).
        let label = if self.line_terminator_before_current() {
            None
        } else if let Token::Ident(name) = self.current() {
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

        // Destructuring assignment statement: `[a, b] = e` / `({a} = e)`.
        // Desugar to a block that binds the RHS to a temp once, then
        // assigns each existing target by index / property.
        if let Expr::Assign {
            op: AssignOp::Assign,
            left,
            right,
            ..
        } = &expression
        {
            if matches!(left.as_ref(), Expr::Array { .. } | Expr::Object { .. }) {
                if let Some(pattern) = Self::expr_to_pattern(left) {
                    let mut body = Vec::new();
                    self.desugar_pattern_assign(&pattern, (**right).clone(), &mut body);
                    return Ok(Stmt::Block {
                        body,
                        span: Span::new(start, self.prev_span().end),
                    });
                }
            }
        }

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
                // A plain `=` onto an array/object literal is a
                // *destructuring assignment* (`[a, b] = e`, `({a} = e)`),
                // desugared at statement level. Allow it through here when
                // the literal is a valid pattern; reject everything else.
                let is_destructuring = matches!(op, AssignOp::Assign)
                    && matches!(expr, Expr::Array { .. } | Expr::Object { .. })
                    && Self::expr_to_pattern(&expr).is_some();
                if !is_destructuring {
                    return Err(ParseError::InvalidAssignmentTarget { span }.into());
                }
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
            Token::QuestionQuestionEq => Some(AssignOp::NullishAssign),
            Token::AndEq => Some(AssignOp::LogicalAndAssign),
            Token::OrEq => Some(AssignOp::LogicalOrAssign),
            _ => None,
        }
    }

    fn parse_conditional_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        let test = self.parse_nullish_expression()?;

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

    /// Parse `??` chains. Sits below the conditional and above the
    /// binary precedence ladder — `??` binds looser than `||` (so
    /// `a || b ?? c` is `(a || b) ?? c`) and tighter than `?:`.
    /// Left-associative: `a ?? b ?? c` ≡ `(a ?? b) ?? c`.
    fn parse_nullish_expression(&mut self) -> Result<Expr> {
        let mut left = self.parse_binary_expression(0)?;
        while self.check(&Token::QuestionQuestion) {
            self.advance();
            let right = self.parse_binary_expression(0)?;
            let span = Span::new(left.span().start, right.span().end);
            left = Expr::NullishCoalesce {
                left: Box::new(left),
                right: Box::new(right),
                span,
            };
        }
        Ok(left)
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
            // `delete` parses successfully. The inference pass emits a
            // soft diagnostic (`delete` isn't modelled by the row
            // algebra: see `infer_unary`) and returns `Type::Error`,
            // which prevents the result from being mistakenly trusted
            // downstream. We accept it at parse time so a single
            // `delete` in the middle of an otherwise checkable file
            // (htmx, jQuery, lodash, …) doesn't abort the whole run.
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
                    expected: "expression (await is only valid inside an async function)"
                        .to_string(),
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

        // Postfix ++/--. ASI: a line terminator between the operand
        // and the operator causes a semicolon to be inserted, so the
        // operator becomes a *prefix* on the next statement instead.
        if self.line_terminator_before_current() {
            return Ok(expr);
        }
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

        // `new` produces either a NewTarget meta-property or a `new X(...)`
        // construction. After construction we fall through to the call/
        // member chain loop below so trailing `.foo`, `[k]`, `(args)`, and
        // `?.` segments compose normally (`new URL(p, b).pathname`,
        // `new FormData(elt).forEach(...)`, etc.).
        let mut expr = if self.consume_if(&Token::New) {
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

            Expr::New {
                callee: Box::new(callee),
                arguments,
                span: Span::new(start, self.prev_span().end),
            }
        } else {
            self.parse_member_expression()?
        };

        // Handle call and member expressions, including optional-chain
        // links. Once we see the first `?.` the chain switches to an
        // `OptionalChain` accumulator and all subsequent `.x` / `[k]` /
        // `(args)` and `?.` segments fold into it so the short-circuit
        // propagates over the whole tail.
        let mut chain_segments: Option<Vec<crate::ast::ChainSegment>> = None;

        loop {
            // `?.` — the chain switch. Subsequent forms get folded into
            // the segment list rather than wrapped as separate AST
            // nodes. The next-segment shape is determined by the token
            // immediately after `?.`: `(` for an optional call, `[` for
            // an optional computed access, otherwise an optional member.
            if self.check(&Token::QuestionDot) {
                self.advance();
                let segments = chain_segments.get_or_insert_with(Vec::new);
                let seg_start = self.prev_span().start;
                if self.consume_if(&Token::LParen) {
                    let arguments = self.parse_arguments()?;
                    segments.push(crate::ast::ChainSegment::Call {
                        arguments,
                        optional: true,
                        span: Span::new(seg_start, self.prev_span().end),
                    });
                } else if self.consume_if(&Token::LBracket) {
                    let property = self.parse_expression()?;
                    self.expect(&Token::RBracket)?;
                    segments.push(crate::ast::ChainSegment::Computed {
                        property: Box::new(property),
                        optional: true,
                        span: Span::new(seg_start, self.prev_span().end),
                    });
                } else {
                    // `?.foo` regular ident/keyword or `?.#name`
                    // private. Same private-name sentinel lowering as
                    // the non-optional dot arm.
                    let property = if let Token::PrivateIdent(name) = self.current().clone() {
                        self.advance();
                        Self::private_name(&name)
                    } else {
                        self.expect_ident_or_keyword()?
                    };
                    segments.push(crate::ast::ChainSegment::Member {
                        property,
                        optional: true,
                        span: Span::new(seg_start, self.prev_span().end),
                    });
                }
                continue;
            }

            if self.consume_if(&Token::LParen) {
                let arguments = self.parse_arguments()?;
                if let Some(segments) = chain_segments.as_mut() {
                    segments.push(crate::ast::ChainSegment::Call {
                        arguments,
                        optional: false,
                        span: Span::new(start, self.prev_span().end),
                    });
                } else {
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        arguments,
                        keywords: vec![],
                        span: Span::new(start, self.prev_span().end),
                    };
                }
            } else if self.consume_if(&Token::Dot) {
                // `.foo` (regular ident or keyword) or `.#name`
                // (private). Both lower into the same `Expr::Member`
                // shape; private names go through the sentinel
                // lowering so they can't be reached from outside the
                // class body.
                let property = if let Token::PrivateIdent(name) = self.current().clone() {
                    if self.class_depth == 0 {
                        let span = self.current_span();
                        return Err(ParseError::UnexpectedToken {
                            found: format!("#{}", name),
                            expected: "identifier (private member access #name is only \
                                allowed inside a class body)"
                                .to_string(),
                            span,
                        }
                        .into());
                    }
                    self.advance();
                    Self::private_name(&name)
                } else {
                    self.expect_ident_or_keyword()?
                };
                if let Some(segments) = chain_segments.as_mut() {
                    segments.push(crate::ast::ChainSegment::Member {
                        property,
                        optional: false,
                        span: Span::new(start, self.prev_span().end),
                    });
                } else {
                    expr = Expr::Member {
                        object: Box::new(expr),
                        property,
                        span: Span::new(start, self.prev_span().end),
                    };
                }
            } else if self.consume_if(&Token::LBracket) {
                let property = self.parse_expression()?;
                self.expect(&Token::RBracket)?;
                if let Some(segments) = chain_segments.as_mut() {
                    segments.push(crate::ast::ChainSegment::Computed {
                        property: Box::new(property),
                        optional: false,
                        span: Span::new(start, self.prev_span().end),
                    });
                } else {
                    expr = Expr::ComputedMember {
                        object: Box::new(expr),
                        property: Box::new(property),
                        span: Span::new(start, self.prev_span().end),
                    };
                }
            } else {
                break;
            }
        }

        if let Some(segments) = chain_segments {
            expr = Expr::OptionalChain {
                head: Box::new(expr),
                segments,
                span: Span::new(start, self.prev_span().end),
            };
        }

        Ok(expr)
    }

    fn parse_member_expression(&mut self) -> Result<Expr> {
        let start = self.current_span().start;
        let mut expr = self.parse_primary_expression()?;

        loop {
            if self.consume_if(&Token::Dot) {
                let property = if let Token::PrivateIdent(name) = self.current().clone() {
                    if self.class_depth == 0 {
                        let span = self.current_span();
                        return Err(ParseError::UnexpectedToken {
                            found: format!("#{}", name),
                            expected: "identifier (private member access #name is only \
                                allowed inside a class body)"
                                .to_string(),
                            span,
                        }
                        .into());
                    }
                    self.advance();
                    Self::private_name(&name)
                } else {
                    self.expect_ident_or_keyword()?
                };
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
                if self.check(&Token::DotDotDot) {
                    // `...expr` spread argument. The runtime semantics
                    // (flatten into N arguments) aren't representable
                    // in inty's fixed-arity call model. We parse the
                    // spread into an `Expr::Spread`; `infer_call` peels
                    // the wrapper off and treats the inner expression
                    // as a single argument, which gives a useful error
                    // when arities mismatch but lets variadic-style
                    // code parse.
                    let spread_start = self.current_span().start;
                    self.advance();
                    let argument = self.parse_assignment_expression()?;
                    let spread_span = Span::new(spread_start, self.prev_span().end);
                    args.push(Expr::Spread {
                        argument: Box::new(argument),
                        span: spread_span,
                    });
                } else {
                    args.push(self.parse_assignment_expression()?);
                }

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
            } else if self.check(&Token::DotDotDot) {
                let spread_start = self.current_span().start;
                self.advance();
                let argument = self.parse_assignment_expression()?;
                let spread_span = Span::new(spread_start, self.prev_span().end);
                elements.push(Some(Expr::Spread {
                    argument: Box::new(argument),
                    span: spread_span,
                }));
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

        // JSDoc `@type` annotation directly preceding this property.
        // Recorded by the scanner with an empty name + JsDoc kind so we
        // attach it to the NEXT named binding rather than the previous
        // one (the inline `/*: T */` form attaches backwards). Captured
        // here unconditionally so spreads and methods can still pick it
        // up if needed; today we only thread it through Property nodes.
        let pending_jsdoc = self.try_get_jsdoc_type_annotation(self.current_span());

        // `...expr` spread element. Right-bias is implicit in the
        // typing rule: properties later in source order win.
        if self.check(&Token::DotDotDot) {
            self.advance();
            let argument = self.parse_assignment_expression()?;
            return Ok(PropDef::Spread {
                argument,
                span: Span::new(start, self.prev_span().end),
            });
        }

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
                return_type_ast: None,
                span: Span::new(start, self.prev_span().end),
            });
        }

        // Property shorthand: `{ name }` is `{ name: name }`. The key
        // must be an identifier (string/number keys can't carry the
        // implicit reference to a same-named binding). Triggers when
        // the next token closes the entry (`,` or `}`) without an
        // intervening `:`.
        if let PropKey::Ident(name) = &key {
            if self.check(&Token::Comma) || self.check(&Token::RBrace) {
                let key_span = self.prev_span();
                return Ok(PropDef::Property {
                    key: key.clone(),
                    value: Expr::Ident {
                        name: name.clone(),
                        span: key_span,
                    },
                    type_annotation: pending_jsdoc,
                    span: Span::new(start, self.prev_span().end),
                });
            }
        }

        // Per-field type annotation: `key /*: T */: value`. We look it up by
        // the key name *before* consuming the colon, so the scanner's
        // `last_ident = key` at the time of the `/*:` lines up. The
        // inline form wins over a preceding JSDoc `@type` if both are
        // present (the user is being more specific) — that's the same
        // tie-break the class-body field parser uses (see line ~1146).
        let inline_annotation = if let PropKey::Ident(name) = &key {
            self.try_get_type_annotation(self.current_span(), name)
        } else {
            None
        };
        let type_annotation = inline_annotation.or(pending_jsdoc);

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
                | Token::Class
                | Token::Extends
                | Token::Super
                | Token::Async
                | Token::Await
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
    /// function? Accepts `ident =>`, `() =>`, and `(ident [, ident]*) =>`,
    /// plus the same forms prefixed with `async`. Does not consume
    /// anything. `async` is a reserved keyword in this lexer, so there's
    /// no ambiguity with a value bound to `async`.
    fn looks_like_arrow_function(&self) -> bool {
        let head_offset = if matches!(self.current(), Token::Async) {
            1
        } else {
            0
        };
        let head = self.tokens.get(self.pos + head_offset).map(|s| &s.value);

        // Simple param: `ident =>`
        if matches!(head, Some(Token::Ident(_))) {
            return self
                .tokens
                .get(self.pos + head_offset + 1)
                .map(|s| matches!(s.value, Token::FatArrow))
                .unwrap_or(false);
        }

        // Parenthesised params: `(` ... `)` `=>`. We only need to know
        // whether the matching `)` is immediately followed by `=>`, so we
        // track nesting for every kind of bracket and ignore everything
        // else. Pattern parameters (`({x})`, `([a, b])`) go through here
        // just fine — the inner braces/brackets are balanced like any
        // other group.
        if matches!(head, Some(Token::LParen)) {
            let mut i = self.pos + head_offset + 1;
            let mut paren_depth: i32 = 1;
            let mut brace_depth: i32 = 0;
            let mut bracket_depth: i32 = 0;
            while let Some(tok) = self.tokens.get(i) {
                match &tok.value {
                    Token::LParen => paren_depth += 1,
                    Token::RParen => {
                        paren_depth -= 1;
                        if paren_depth == 0 && brace_depth == 0 && bracket_depth == 0 {
                            return self
                                .tokens
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
    /// An `async` prefix lifts the body into an IIFE handed to
    /// `Promise.resolve`, matching the rewrite that
    /// [`Self::make_async_function_decl`] applies to async function
    /// declarations.
    fn parse_arrow_function(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        // Optional `async` prefix. `looks_like_arrow_function` has
        // already confirmed an arrow head follows.
        if matches!(self.current(), Token::Async) {
            self.advance();
            self.next_fn_is_async = true;
        }

        // Parse parameters.
        let (params, prefix): (Vec<Param>, Vec<Stmt>) = if matches!(self.current(), Token::Ident(_))
        {
            // Single-identifier form: `x => ...`
            let name_span = self.current_span();
            let name = self.expect_ident()?;
            let span = Span::new(name_span.start, name_span.start + name.len());
            (vec![Param::new(name, span)], vec![])
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

        let span = Span::new(start, self.prev_span().end);
        let body = if is_async {
            Self::wrap_body_in_promise_resolve(body, span)
        } else {
            body
        };

        Ok(Expr::Function {
            name: None,
            params,
            body,
            type_annotation: None,
            span,
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

    /// True if the byte range between the previous token's end and the
    /// current token's start contains a line terminator (LF / CR).
    /// Used by the ASI rules in `parse_return` / `parse_break` /
    /// `parse_continue` / `parse_throw` and by the postfix `++` / `--`
    /// arm to decide whether the next token belongs to the same
    /// statement.
    fn line_terminator_before_current(&self) -> bool {
        if self.source.is_empty() {
            return false;
        }
        let prev_end = self.prev_span().end;
        let cur_start = self.current_span().start;
        if cur_start <= prev_end {
            return false;
        }
        let between = &self.source.as_bytes()
            [prev_end.min(self.source.len())..cur_start.min(self.source.len())];
        between.iter().any(|&b| b == b'\n' || b == b'\r')
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

    /// Identifier or the keyword `default`. Used for names inside
    /// `export { … }` (and eventually `import { … }`) clauses where
    /// `default` is permitted to interoperate with `export default`.
    fn expect_module_name(&mut self) -> Result<String> {
        match self.current().clone() {
            Token::Ident(name) => {
                self.advance();
                Ok(name)
            }
            Token::Default => {
                self.advance();
                Ok("default".to_string())
            }
            _ => Err(ParseError::UnexpectedToken {
                found: format!("{}", self.current()),
                expected: "identifier or `default`".to_string(),
                span: self.current_span(),
            }
            .into()),
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
                    return Some(ann.clone());
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
    fn try_get_type_annotation_for_function(
        &mut self,
        before_span: Span,
        name: &str,
    ) -> Option<TypeAnnotation> {
        // Look for a type annotation that ends before this position and matches the name
        while self.annotation_pos < self.type_annotations.len() {
            let ann = &self.type_annotations[self.annotation_pos];
            if ann.span.end <= before_span.start {
                if ann.name == name {
                    self.annotation_pos += 1;
                    return Some(ann.clone());
                }
                // Skip annotations that don't match
                self.annotation_pos += 1;
                continue;
            }
            break;
        }
        None
    }

    /// Try to get a JSDoc `@type` annotation (recorded by the scanner
    /// with `kind = JsDoc` and an empty `name`, signifying "attaches
    /// to the next binding") that ends before the given position.
    /// Consumes the annotation if found, returning it for the caller
    /// to attach to whichever property / declarator opens next.
    fn try_get_jsdoc_type_annotation(&mut self, before_span: Span) -> Option<TypeAnnotation> {
        while self.annotation_pos < self.type_annotations.len() {
            let ann = &self.type_annotations[self.annotation_pos];
            if ann.span.end > before_span.start {
                break;
            }
            if ann.kind == AnnotationKind::JsDoc && ann.name.is_empty() {
                self.annotation_pos += 1;
                return Some(ann.clone());
            }
            // Non-JSDoc annotation that didn't match by name at its
            // expected attach point — skip so we keep scanning.
            self.annotation_pos += 1;
        }
        None
    }
}

/// Parse source code into an AST
pub fn parse(source: &str) -> Result<Program> {
    use crate::frontends::javascript::lexer::Scanner;

    let scanner = Scanner::new(source);
    let (tokens, type_annotations, type_aliases) = scanner.tokenize()?;

    let mut parser = Parser::with_source(tokens, type_annotations, source.to_string());
    let mut program = parser.parse_program()?;
    program.type_aliases = type_aliases;
    Ok(program)
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
        let program = parse("import init, { check_types } from './pkg/inty.js';").unwrap();
        if let Stmt::Import {
            specifiers, source, ..
        } = &program.statements[0]
        {
            assert_eq!(source, "./pkg/inty.js");
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

    // ----- P4: class field declarations + modifier tolerance -----

    fn parse_class_factory(source: &str) -> Vec<PropDef> {
        let program = parse(source).unwrap();
        // The class declaration desugars to `function Name(args) { return { ... }; }`.
        let stmt = program.statements.last().unwrap();
        if let Stmt::FunctionDecl { body, .. } = stmt {
            if let Stmt::Block { body, .. } = body.as_ref() {
                if let Some(Stmt::Return {
                    argument: Some(Expr::Object { properties, .. }),
                    ..
                }) = body.last()
                {
                    return properties.clone();
                }
            }
        }
        panic!(
            "class did not desugar to expected factory function shape: {:?}",
            stmt
        );
    }

    #[test]
    fn class_fields_with_initializers_become_props() {
        let props = parse_class_factory("class C { a = 0; b = \"hi\"; c = []; constructor() {} }");
        let names: Vec<_> = props
            .iter()
            .filter_map(|p| match p {
                PropDef::Property {
                    key: PropKey::Ident(n),
                    ..
                } => Some(n.clone()),
                _ => None,
            })
            .collect();
        assert!(names.contains(&"a".to_string()));
        assert!(names.contains(&"b".to_string()));
        assert!(names.contains(&"c".to_string()));
    }

    #[test]
    fn class_modifier_tolerance() {
        // Modifiers parse and are erased. Constructor still gets the field
        // values via `this.NAME = …`, so the desugared object literal has
        // the fields.
        let props = parse_class_factory(
            "class C { private name; private count = 0; readonly tag = \"c\"; \
             constructor(name) { this.name = name; } }",
        );
        let names: Vec<_> = props
            .iter()
            .filter_map(|p| match p {
                PropDef::Property {
                    key: PropKey::Ident(n),
                    ..
                } => Some(n.clone()),
                _ => None,
            })
            .collect();
        assert!(names.contains(&"name".to_string()));
        assert!(names.contains(&"count".to_string()));
        assert!(names.contains(&"tag".to_string()));
    }

    #[test]
    fn class_ts_inline_annotation_attaches_to_field() {
        // The TS-style `: Number` annotation on a field declaration
        // becomes a TypeAnnotation whose name matches the field name.
        let props = parse_class_factory("class C { count: Number = 0; constructor() {} }");
        let count_prop = props
            .iter()
            .find(|p| {
                matches!(
                    p,
                    PropDef::Property { key: PropKey::Ident(n), .. } if n == "count"
                )
            })
            .expect("count field");
        if let PropDef::Property {
            type_annotation, ..
        } = count_prop
        {
            let ann = type_annotation.as_ref().expect("annotation present");
            assert_eq!(ann.name, "count");
            assert_eq!(ann.content.trim(), "Number");
        } else {
            panic!("expected Property");
        }
    }

    #[test]
    fn class_ts_annotation_moves_to_constructor_assignment() {
        // A declaration-only annotated field with a constructor that
        // sets it: the annotation moves to the constructor-extracted
        // property so the constructor parameter gets type-checked
        // against the declared type.
        let props = parse_class_factory(
            "class C { name: String; constructor(name) { this.name = name; } }",
        );
        let name_prop = props
            .iter()
            .find(|p| {
                matches!(
                    p,
                    PropDef::Property { key: PropKey::Ident(n), .. } if n == "name"
                )
            })
            .expect("name field");
        if let PropDef::Property {
            value,
            type_annotation,
            ..
        } = name_prop
        {
            assert!(matches!(value, Expr::Ident { .. }));
            let ann = type_annotation.as_ref().expect("annotation moved");
            assert_eq!(ann.name, "name");
            assert_eq!(ann.content.trim(), "String");
        } else {
            panic!("expected Property");
        }
    }

    #[test]
    fn class_duplicate_field_rejected() {
        let result = parse("class C { a; a = 1; constructor() {} }");
        let err = result.expect_err("duplicate field should error");
        let msg = format!("{:?}", err);
        assert!(msg.contains("duplicate field"), "got: {}", msg);
    }

    #[test]
    fn class_field_array_type_annotation() {
        // Array brackets in the type don't terminate the type span
        // (depth-counting on `[ ]`).
        let props = parse_class_factory("class C { items: Item[] = []; constructor() {} }");
        let prop = props
            .iter()
            .find(|p| {
                matches!(
                    p,
                    PropDef::Property { key: PropKey::Ident(n), .. } if n == "items"
                )
            })
            .expect("items field");
        if let PropDef::Property {
            type_annotation, ..
        } = prop
        {
            let ann = type_annotation.as_ref().expect("annotation");
            assert_eq!(ann.content.trim(), "Item[]");
        }
    }
}
