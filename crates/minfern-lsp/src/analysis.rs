//! Run minfern's lex/parse/infer pipeline on an in-memory document and
//! expose the results in a form the LSP server can query.

use lsp_types::{CompletionItem, CompletionItemKind};

use minfern::error::MinfernError;
use minfern::infer::{InferState, TypeEnv};
use minfern::lexer::{Scanner, Span, Token};
use minfern::parser::ast::{Expr, Program, Stmt};
use minfern::parser::Parser;
use minfern::stdlib::initial_env_with_stdlib;
use minfern::types::{PrettyContext, RowType, Type};

use crate::resolver::Resolution;

/// Result of checking one document: the errors found and (when the
/// program parsed) the inference state needed to answer hover queries.
pub struct Analysis {
    pub errors: Vec<MinfernError>,
    program: Option<Program>,
    final_env: Option<TypeEnv>,
    state: Option<InferState>,
    pub resolution: Resolution,
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

        // Resolve identifiers (independent of type inference). We pass
        // the text length so the module scope covers EOF — otherwise
        // queries past the last statement (a blank line at the end of
        // the file) would find no scope.
        let resolution = Resolution::build_with_len(&program, text.len());

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
                    resolution,
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
                    resolution,
                }
            }
            Err(e) => {
                errors.push(e);
                Analysis {
                    errors,
                    program: Some(program),
                    final_env: None,
                    state: Some(state),
                    resolution,
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
            resolution: Resolution::default(),
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

    /// Format the type of `name` (looked up in the final env) as a
    /// short string, for use as completion-item `detail`. Returns
    /// `None` if the name isn't visible.
    pub fn type_of_name(&self, name: &str) -> Option<String> {
        let env = self.final_env.as_ref()?;
        let state = self.state.as_ref()?;
        let scheme = env.lookup(name)?;
        let applied = state.apply_subst(scheme);
        let mut ctx = PrettyContext::new();
        Some(ctx.format_scheme(&applied))
    }

    /// If the byte just before `offset` is `.` and the preceding
    /// identifier resolves to a row type, return one completion item
    /// per property.
    ///
    /// Works on raw text (not the AST) so it still fires when the
    /// program is mid-edit and doesn't parse — e.g. the user just
    /// typed `obj.` and the trailing dot makes it incomplete. In that
    /// case we re-run [`Analysis::check`] with the trailing `.`
    /// replaced by `;` to get a usable env.
    pub fn member_completions_before_with(
        &self,
        text: &str,
        offset: usize,
    ) -> Option<Vec<CompletionItem>> {
        // Walk back over identifier-suffix chars (so we correctly find
        // `.` even if the user has started typing a property name).
        let mut end = offset.min(text.len());
        let bytes = text.as_bytes();
        while end > 0 && is_ident_byte(bytes[end - 1]) {
            end -= 1;
        }
        if end == 0 || bytes[end - 1] != b'.' {
            return None;
        }
        // The object expression sits before the dot.
        let mut start = end - 1;
        while start > 0 && is_ident_byte(bytes[start - 1]) {
            start -= 1;
        }
        if start == end - 1 {
            return None;
        }
        let obj_name = text[start..end - 1].to_string();

        // Try the current Analysis first; fall back to a recovery check.
        if let Some(items) = self.lookup_member_props(&obj_name) {
            return Some(items);
        }
        let mut patched = text.to_string();
        // Replace the offending `.` with `;` so the program parses.
        patched.replace_range((end - 1)..end, ";");
        let recovery = Analysis::check(&patched);
        recovery.lookup_member_props(&obj_name)
    }

    fn lookup_member_props(&self, obj_name: &str) -> Option<Vec<CompletionItem>> {
        let env = self.final_env.as_ref()?;
        let state = self.state.as_ref()?;
        let scheme = env.lookup(obj_name)?;
        let ty = state.apply_subst(&scheme.body.ty);
        let row = row_of(&ty)?;
        let items: Vec<CompletionItem> = row
            .props
            .iter()
            .map(|(name, prop_ty)| {
                let mut ctx = PrettyContext::new();
                CompletionItem {
                    label: name.0.clone(),
                    kind: Some(CompletionItemKind::FIELD),
                    detail: Some(ctx.format_type(prop_ty)),
                    ..Default::default()
                }
            })
            .collect();
        Some(items)
    }

    /// Compute signature help if the cursor sits inside a function
    /// call's argument list. Returns the parameter labels and which
    /// one the cursor is currently on.
    pub fn signature_help_at(&self, text: &str, offset: usize) -> Option<SignatureInfo> {
        let program = self.program.as_ref()?;
        let env = self.final_env.as_ref()?;
        let state = self.state.as_ref()?;

        // Find the innermost call expression containing offset.
        let call = innermost_call_at(program, offset)?;
        let (callee_name, paren_open) = call_descriptor(call, text)?;

        // Look up the callee's type (only Ident callees in v1).
        let scheme = env.lookup(callee_name.as_str())?;
        let ty = state.apply_subst(&scheme.body.ty);
        let (params, ret) = func_params(&ty)?;

        let mut ctx = PrettyContext::new();
        let param_labels: Vec<String> = params.iter().map(|p| ctx.format_type(p)).collect();
        let ret_label = ctx.format_type(&ret);
        let signature_label = format!(
            "{}({}): {}",
            callee_name,
            param_labels.join(", "),
            ret_label,
        );

        let active = active_arg_index(text, paren_open + 1, offset, params.len());
        Some(SignatureInfo {
            signature_label,
            parameters: param_labels,
            active_parameter: active as u32,
        })
    }
}

/// Result of a successful hover lookup.
pub struct HoverResult {
    pub name: String,
    pub span: Span,
    pub type_str: String,
}

/// Result of a successful signature-help lookup.
pub struct SignatureInfo {
    pub signature_label: String,
    pub parameters: Vec<String>,
    pub active_parameter: u32,
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

/// Strip leading variable substitutions / row applications and return a
/// [`RowType`] reference if `ty` is a row.
fn row_of(ty: &Type) -> Option<&RowType> {
    if let Type::Row(r) = ty {
        Some(r)
    } else {
        None
    }
}

/// Pull the parameter list and return type out of a function type.
/// `apply_subst` should already have been called on `ty`.
fn func_params(ty: &Type) -> Option<(Vec<Type>, Type)> {
    if let Type::Func { params, ret, .. } = ty {
        Some((params.clone(), (**ret).clone()))
    } else {
        None
    }
}

/// Walk all `Expr::Call` nodes in the program and return a reference
/// to the innermost one whose span contains `offset` (and whose
/// argument list opens before `offset`).
fn innermost_call_at(program: &Program, offset: usize) -> Option<&Expr> {
    let mut best: Option<&Expr> = None;
    for stmt in &program.statements {
        find_call(stmt, offset, &mut best);
    }
    best
}

fn find_call<'a>(stmt: &'a Stmt, offset: usize, best: &mut Option<&'a Expr>) {
    match stmt {
        Stmt::Expr { expression, .. } => find_call_expr(expression, offset, best),
        Stmt::Var { declarations, .. } => {
            for d in declarations {
                if let Some(init) = &d.init {
                    find_call_expr(init, offset, best);
                }
            }
        }
        Stmt::Block { body, .. } => {
            for s in body {
                find_call(s, offset, best);
            }
        }
        Stmt::If { test, consequent, alternate, .. } => {
            find_call_expr(test, offset, best);
            find_call(consequent, offset, best);
            if let Some(a) = alternate {
                find_call(a, offset, best);
            }
        }
        Stmt::While { test, body, .. } | Stmt::DoWhile { test, body, .. } => {
            find_call_expr(test, offset, best);
            find_call(body, offset, best);
        }
        Stmt::For { body, .. } => find_call(body, offset, best),
        Stmt::Return { argument: Some(e), .. } | Stmt::Throw { argument: e, .. } => {
            find_call_expr(e, offset, best);
        }
        Stmt::FunctionDecl { body, .. } => find_call(body, offset, best),
        _ => {}
    }
}

fn find_call_expr<'a>(expr: &'a Expr, offset: usize, best: &mut Option<&'a Expr>) {
    if !span_contains(expr.span(), offset) {
        return;
    }
    if let Expr::Call { arguments, .. } = expr {
        // This call contains the cursor; record it (overwriting any
        // outer call). Then descend into args / callee for nested
        // calls.
        *best = Some(expr);
        if let Expr::Call { callee, .. } = expr {
            find_call_expr(callee, offset, best);
        }
        for a in arguments {
            find_call_expr(a, offset, best);
        }
        return;
    }
    match expr {
        Expr::Call { callee, arguments, .. } | Expr::New { callee, arguments, .. } => {
            find_call_expr(callee, offset, best);
            for a in arguments {
                find_call_expr(a, offset, best);
            }
        }
        Expr::Binary { left, right, .. } | Expr::Assign { left, right, .. } => {
            find_call_expr(left, offset, best);
            find_call_expr(right, offset, best);
        }
        Expr::Unary { argument, .. } => find_call_expr(argument, offset, best),
        Expr::Member { object, .. } => find_call_expr(object, offset, best),
        Expr::ComputedMember { object, property, .. } => {
            find_call_expr(object, offset, best);
            find_call_expr(property, offset, best);
        }
        Expr::Conditional { test, consequent, alternate, .. } => {
            find_call_expr(test, offset, best);
            find_call_expr(consequent, offset, best);
            find_call_expr(alternate, offset, best);
        }
        Expr::Sequence { expressions, .. } | Expr::TemplateLiteral { expressions, .. } => {
            for e in expressions {
                find_call_expr(e, offset, best);
            }
        }
        Expr::Array { elements, .. } => {
            for e in elements.iter().flatten() {
                find_call_expr(e, offset, best);
            }
        }
        _ => {}
    }
}

/// Pull `(callee_name, paren_open_byte)` out of an `Expr::Call`. v1
/// only handles bare-identifier callees.
fn call_descriptor(call: &Expr, text: &str) -> Option<(String, usize)> {
    let (callee, span) = match call {
        Expr::Call { callee, span, .. } => (callee, span),
        _ => return None,
    };
    let name = match callee.as_ref() {
        Expr::Ident { name, .. } => name.clone(),
        _ => return None,
    };
    // Find the `(` after the callee. The callee's span ends right
    // before any whitespace and the paren.
    let search_start = callee.span().end;
    let search_end = span.end.min(text.len());
    let bytes = text.as_bytes();
    let paren = (search_start..search_end).find(|&i| bytes[i] == b'(')?;
    Some((name, paren))
}

/// Count top-level commas between `start` (just past the `(`) and
/// `cursor`, ignoring commas nested inside parens / brackets / braces.
fn active_arg_index(text: &str, start: usize, cursor: usize, max: usize) -> usize {
    let bytes = text.as_bytes();
    let end = cursor.min(text.len());
    let mut depth: i32 = 0;
    let mut count = 0usize;
    for i in start..end {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth = (depth - 1).max(0),
            b',' if depth == 0 => count += 1,
            _ => {}
        }
    }
    if max == 0 {
        0
    } else {
        count.min(max - 1)
    }
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
