//! Run minfern's lex/parse/infer pipeline on an in-memory document and
//! expose the results in a form the LSP server can query.

use minfern::error::MinfernError;
use minfern::infer::{InferState, TypeEnv};
use minfern::lexer::{Scanner, Span, Token};
use minfern::parser::ast::{Expr, Program, Stmt};
use minfern::parser::Parser;
use minfern::stdlib::initial_env_with_stdlib;
use minfern::types::PrettyContext;

/// Result of checking one document: the errors found and (when the
/// program parsed) the inference state needed to answer hover queries.
pub struct Analysis {
    pub errors: Vec<MinfernError>,
    program: Option<Program>,
    final_env: Option<TypeEnv>,
    state: Option<InferState>,
}

impl Analysis {
    /// Lex, parse, and infer `text`. Always returns an `Analysis`; on any
    /// error the relevant fields are left empty.
    pub fn check(text: &str) -> Self {
        let mut errors = Vec::new();

        // Lex.
        let mut scanner = Scanner::new(text);
        let mut tokens = Vec::new();
        loop {
            match scanner.next_token() {
                Ok(tok) => {
                    let is_eof = matches!(tok.value, Token::Eof);
                    tokens.push(tok);
                    if is_eof {
                        break;
                    }
                }
                Err(e) => {
                    errors.push(e);
                    return Analysis::errors_only(errors);
                }
            }
        }

        // Parse.
        let type_annotations = scanner.type_annotations().to_vec();
        let mut parser = Parser::new(tokens, type_annotations);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(e) => {
                errors.push(e);
                return Analysis::errors_only(errors);
            }
        };

        // Build the initial env with the embedded stdlib. If the stdlib
        // itself fails to load (shouldn't happen — it's tested), we
        // surface the error and bail out of inference.
        let (env, mut state) = match initial_env_with_stdlib() {
            Ok(r) => r,
            Err(e) => {
                errors.push(e);
                return Analysis {
                    errors,
                    program: Some(program),
                    final_env: None,
                    state: None,
                };
            }
        };

        // Infer.
        match state.infer_program_with_env(&env, &program) {
            Ok((_ty, final_env)) => {
                if let Err(e) = state.resolve_constraints() {
                    errors.push(e);
                }
                Analysis {
                    errors,
                    program: Some(program),
                    final_env: Some(final_env),
                    state: Some(state),
                }
            }
            Err(e) => {
                errors.push(e);
                Analysis {
                    errors,
                    program: Some(program),
                    final_env: None,
                    state: Some(state),
                }
            }
        }
    }

    fn errors_only(errors: Vec<MinfernError>) -> Self {
        Analysis {
            errors,
            program: None,
            final_env: None,
            state: None,
        }
    }

    /// If an identifier covers `byte_offset`, return its inferred type
    /// formatted as a string.
    ///
    /// v1 limitation: the lookup uses the *final* environment, so for a
    /// shadowed binding the deepest definition wins regardless of where
    /// the cursor sits. Good enough until per-position env snapshots
    /// arrive.
    pub fn hover_at(&self, byte_offset: usize) -> Option<HoverResult> {
        let program = self.program.as_ref()?;
        let env = self.final_env.as_ref()?;
        let state = self.state.as_ref()?;

        let (name, span) = find_identifier(program, byte_offset)?;
        let scheme = env.lookup(&name)?;
        let applied_scheme = state.apply_subst(scheme);
        let mut ctx = PrettyContext::new();
        let formatted = ctx.format_scheme(&applied_scheme);
        Some(HoverResult {
            name,
            span,
            type_str: formatted,
        })
    }
}

/// Result of a successful hover lookup.
pub struct HoverResult {
    pub name: String,
    pub span: Span,
    pub type_str: String,
}

/// Walk the program looking for the smallest `Expr::Ident` whose span
/// contains `offset`. Returns the identifier name and its span.
fn find_identifier(program: &Program, offset: usize) -> Option<(String, Span)> {
    let mut best: Option<(String, Span)> = None;
    for stmt in &program.statements {
        visit_stmt(stmt, offset, &mut best);
    }
    best
}

fn visit_stmt(stmt: &Stmt, offset: usize, best: &mut Option<(String, Span)>) {
    match stmt {
        Stmt::Var { declarations, .. } => {
            for d in declarations {
                if span_contains(d.span, offset) {
                    consider(best, d.name.clone(), d.span);
                }
                if let Some(init) = &d.init {
                    visit_expr(init, offset, best);
                }
            }
        }
        Stmt::Expr { expression, .. } => visit_expr(expression, offset, best),
        Stmt::Block { body, .. } => {
            for s in body {
                visit_stmt(s, offset, best);
            }
        }
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
            visit_expr(test, offset, best);
            visit_stmt(consequent, offset, best);
            if let Some(e) = alternate {
                visit_stmt(e, offset, best);
            }
        }
        Stmt::While { test, body, .. } | Stmt::DoWhile { test, body, .. } => {
            visit_expr(test, offset, best);
            visit_stmt(body, offset, best);
        }
        Stmt::For {
            init,
            test,
            update,
            body,
            ..
        } => {
            if let Some(init) = init {
                use minfern::parser::ast::ForInit;
                match init {
                    ForInit::VarDecl(decls) => {
                        for d in decls {
                            if span_contains(d.span, offset) {
                                consider(best, d.name.clone(), d.span);
                            }
                            if let Some(e) = &d.init {
                                visit_expr(e, offset, best);
                            }
                        }
                    }
                    ForInit::Expr(e) => visit_expr(e, offset, best),
                }
            }
            if let Some(t) = test {
                visit_expr(t, offset, best);
            }
            if let Some(u) = update {
                visit_expr(u, offset, best);
            }
            visit_stmt(body, offset, best);
        }
        Stmt::ForIn { right, body, .. } | Stmt::ForOf { right, body, .. } => {
            visit_expr(right, offset, best);
            visit_stmt(body, offset, best);
        }
        Stmt::Return { argument, .. } => {
            if let Some(v) = argument {
                visit_expr(v, offset, best);
            }
        }
        Stmt::Throw { argument, .. } => visit_expr(argument, offset, best),
        Stmt::Try {
            block,
            handler,
            finalizer,
            ..
        } => {
            visit_stmt(block, offset, best);
            if let Some(h) = handler {
                visit_stmt(&h.body, offset, best);
            }
            if let Some(f) = finalizer {
                visit_stmt(f, offset, best);
            }
        }
        Stmt::Switch {
            discriminant,
            cases,
            ..
        } => {
            visit_expr(discriminant, offset, best);
            for c in cases {
                if let Some(t) = &c.test {
                    visit_expr(t, offset, best);
                }
                for s in &c.consequent {
                    visit_stmt(s, offset, best);
                }
            }
        }
        Stmt::Labeled { body, .. } => visit_stmt(body, offset, best),
        Stmt::FunctionDecl { name, body, span, .. } => {
            if span_contains(*span, offset) {
                consider(best, name.clone(), *span);
            }
            visit_stmt(body, offset, best);
        }
        _ => {}
    }
}

fn visit_expr(expr: &Expr, offset: usize, best: &mut Option<(String, Span)>) {
    if !span_contains(expr.span(), offset) {
        return;
    }
    match expr {
        Expr::Ident { name, span } => consider(best, name.clone(), *span),
        Expr::Array { elements, .. } => {
            for e in elements.iter().flatten() {
                visit_expr(e, offset, best);
            }
        }
        Expr::Object { properties, .. } => {
            use minfern::parser::ast::PropDef;
            for p in properties {
                match p {
                    PropDef::Property { value, .. } => visit_expr(value, offset, best),
                    PropDef::Method { body, .. }
                    | PropDef::Getter { body, .. }
                    | PropDef::Setter { body, .. } => visit_stmt(body, offset, best),
                }
            }
        }
        Expr::Member { object, .. } => visit_expr(object, offset, best),
        Expr::ComputedMember { object, property, .. } => {
            visit_expr(object, offset, best);
            visit_expr(property, offset, best);
        }
        Expr::Call {
            callee, arguments, ..
        }
        | Expr::New {
            callee, arguments, ..
        } => {
            visit_expr(callee, offset, best);
            for a in arguments {
                visit_expr(a, offset, best);
            }
        }
        Expr::Function { body, .. } => visit_stmt(body, offset, best),
        Expr::Unary { argument, .. } => visit_expr(argument, offset, best),
        Expr::Binary { left, right, .. } => {
            visit_expr(left, offset, best);
            visit_expr(right, offset, best);
        }
        Expr::Assign { left, right, .. } => {
            visit_expr(left, offset, best);
            visit_expr(right, offset, best);
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
            visit_expr(test, offset, best);
            visit_expr(consequent, offset, best);
            visit_expr(alternate, offset, best);
        }
        Expr::Sequence { expressions, .. } => {
            for e in expressions {
                visit_expr(e, offset, best);
            }
        }
        Expr::TemplateLiteral { expressions, .. } => {
            for e in expressions {
                visit_expr(e, offset, best);
            }
        }
        _ => {}
    }
}

fn span_contains(span: Span, offset: usize) -> bool {
    span.start <= offset && offset <= span.end
}

fn span_len(span: Span) -> usize {
    span.end.saturating_sub(span.start)
}

fn consider(best: &mut Option<(String, Span)>, name: String, span: Span) {
    match best {
        Some((_, current)) if span_len(*current) <= span_len(span) => {}
        _ => *best = Some((name, span)),
    }
}
