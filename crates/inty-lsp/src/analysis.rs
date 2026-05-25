//! Run inty's lex/parse/infer pipeline on an in-memory document and
//! expose the results in a form the LSP server can query.

use lsp_types::{CompletionItem, CompletionItemKind};

use inty::error::IntyError;
use inty::infer::{InferState, InferWarning, TypeEnv};
use inty::ast::{Expr, ImportSpecifier, Program, Stmt};
use inty::frontends::javascript::lexer::{Scanner, Token};
use inty::frontends::javascript::parser::Parser;
use inty::frontends::Language;
use inty::span::Span;
use inty::stdlib::initial_env_with_stdlib;
use inty::types::{PrettyContext, RowType, Type};

use crate::resolver::Resolution;

/// Result of checking one document: the errors found and (when the
/// program parsed) the inference state needed to answer hover queries.
pub struct Analysis {
    pub errors: Vec<IntyError>,
    program: Option<Program>,
    final_env: Option<TypeEnv>,
    state: Option<InferState>,
    pub resolution: Resolution,
}

impl Analysis {
    /// Lex, parse, and infer `text` as JavaScript. Always returns an
    /// `Analysis`; on any error the relevant fields are left empty.
    pub fn check(text: &str) -> Self {
        Self::check_lang(text, Language::JavaScript)
    }

    /// Like [`Analysis::check`], but for an explicit frontend. The
    /// JavaScript path carries JSDoc type annotations/aliases off the
    /// lexer; the other frontends lower straight to the shared AST.
    pub fn check_lang(text: &str, lang: Language) -> Self {
        let mut errors = Vec::new();

        let program = match lang {
            Language::JavaScript => {
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
                let type_aliases = scanner.type_aliases().to_vec();
                let mut parser = Parser::new(tokens, type_annotations);
                let mut program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        errors.push(e);
                        return Analysis::errors_only(errors);
                    }
                };
                program.type_aliases = type_aliases;
                program
            }
            other => match inty::frontends::parse(other, text) {
                Ok(p) => p,
                Err(e) => {
                    errors.push(e);
                    return Analysis::errors_only(errors);
                }
            },
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

        // Infer. The `Type::Error` recovery path lets inference
        // continue past a failing statement, so `state.errors` may
        // contain multiple diagnostics even though the public API
        // only returns the first via `Result::Err`. Drain the
        // accumulated list so every diagnostic surfaces as an LSP
        // squiggly, not just the first.
        let infer_result = state.infer_program_with_env(&env, &program);
        let collected = state.take_errors();
        match infer_result {
            Ok((_ty, final_env)) => {
                if let Err(e) = state.resolve_constraints() {
                    errors.push(e);
                }
                errors.extend(collected);
                Analysis {
                    errors,
                    program: Some(program),
                    final_env: Some(final_env),
                    state: Some(state),
                    resolution,
                }
            }
            Err(_first) => {
                // `_first` is the head of `collected`; use the
                // accumulated list as-is to avoid duplicating it.
                errors.extend(collected);
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

    /// Non-fatal warnings collected during inference (e.g. unreachable
    /// narrowing branches). Empty if inference didn't run or didn't emit
    /// any.
    pub fn warnings(&self) -> &[InferWarning] {
        match self.state.as_ref() {
            Some(s) => &s.warnings,
            None => &[],
        }
    }

    fn errors_only(errors: Vec<IntyError>) -> Self {
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
    /// Resolution order:
    /// 1. Ask the resolver for the binding at the cursor (handles
    ///    shadowing — inner scopes win).
    /// 2. Look up the binding's type in the inference state's
    ///    `decl_types` map by the binding's name span.
    /// 3. Fall back to `env.lookup(name)` (the final env) for bindings
    ///    we don't yet record per-span — currently catch params and
    ///    named function expressions whose spans the resolver can't
    ///    pin precisely.
    pub fn hover_at(&self, byte_offset: usize) -> Option<HoverResult> {
        let state = self.state.as_ref()?;
        let env = self.final_env.as_ref()?;

        // Try the resolver first — gives shadowing-correct answers and
        // also resolves uses of function parameters that aren't in the
        // final env at all.
        if let Some((def_span, hit_span)) = self.resolution.binding_at(byte_offset) {
            let def = self.resolution.def_at(def_span)?;
            // Prefer the span-keyed scheme: it covers any generalised
            // binding (function decl, `var f = function(...)`, etc.)
            // and is shadow-correct, unlike a name-based env lookup.
            // `decl_types` stores raw `Type` and loses both quantifiers
            // and type-class predicates, so use it only as a fallback.
            if let Some(scheme) = state.get_decl_scheme(def_span) {
                return Some(HoverResult {
                    name: def.name.clone(),
                    span: hit_span,
                    type_str: format_scheme(state.display_scheme(scheme)),
                });
            }
            if let Some(ty) = state.get_decl_type(def_span) {
                return Some(HoverResult {
                    name: def.name.clone(),
                    span: hit_span,
                    type_str: format_type(state.display_type(ty)),
                });
            }
            // Resolver knows the def but inference didn't record a
            // type for it. Fall back to env lookup by name — catches
            // catch params and similar.
            if let Some(scheme) = env.lookup(&def.name) {
                return Some(HoverResult {
                    name: def.name.clone(),
                    span: hit_span,
                    type_str: format_scheme(state.display_scheme(scheme)),
                });
            }
        }

        // Resolver said nothing — fall back to the original AST scan
        // (e.g. for unresolved free identifiers we still want a
        // best-effort type from the final env).
        let program = self.program.as_ref()?;
        let (name, span) = find_identifier(program, byte_offset)?;
        let scheme = env.lookup(&name)?;
        Some(HoverResult {
            name,
            span,
            type_str: format_scheme(state.display_scheme(scheme)),
        })
    }

    /// Format the type of `name` (looked up in the final env) as a
    /// short string, for use as completion-item `detail`. Returns
    /// `None` if the name isn't visible.
    pub fn type_of_name(&self, name: &str) -> Option<String> {
        let env = self.final_env.as_ref()?;
        let state = self.state.as_ref()?;
        let scheme = env.lookup(name)?;
        Some(format_scheme(state.display_scheme(scheme)))
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
        // Tidy the whole row at once so two fields whose types
        // share a tvar get the same letter in the completion list.
        let row_ty = state.display_type(&scheme.body.ty);
        let row = row_of(&row_ty)?;
        let items: Vec<CompletionItem> = row
            .props
            .iter()
            .map(|(name, entry)| CompletionItem {
                label: name.0.clone(),
                kind: Some(CompletionItemKind::FIELD),
                detail: Some(format_type(entry.ty.clone())),
                ..Default::default()
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
        let (callee_expr, call_span) = match call {
            Expr::Call { callee, span, .. } => (callee.as_ref(), *span),
            _ => return None,
        };

        // Resolve the callee's type. Supports plain identifiers and
        // member chains (`obj.method`, `a.b.method`, …); other callee
        // shapes (computed members, calls returning functions) we
        // punt on for v1.
        let (callee_label, callee_ty) = resolve_callee_type(env, state, callee_expr)?;
        // Tidy the callee's whole function type as one unit so
        // params and the return share canonical IDs — `(a, a) =>
        // a` reads as one type, not three independently-tidied
        // pieces.
        let callee_ty = state.display_type(&callee_ty);
        let (params, ret) = func_params(&callee_ty)?;

        // Find the `(` opening the argument list after the callee.
        let bytes = text.as_bytes();
        let search_start = callee_expr.span().end;
        let search_end = call_span.end.min(bytes.len());
        let paren_open = (search_start..search_end).find(|&i| bytes[i] == b'(')?;

        let param_labels: Vec<String> = params.iter().map(|p| format_type(p.clone())).collect();
        let ret_label = format_type(ret.clone());
        let signature_label = format!(
            "{}({}): {}",
            callee_label,
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

    /// Inlay hints for every binding whose name span lies in `[start,
    /// end)`. The returned `label` is the full text the editor should
    /// render — for value bindings (`var x`, parameters, …) it's
    /// `: T`, anchored just after the binding's name; for function
    /// declarations it's `-> Ret`, anchored just after the param
    /// list's closing `)` so the function name itself stays clean and
    /// each parameter still gets its own per-name hint.
    ///
    /// `text` is the source the analysis was built from; we use it
    /// only to find the `)` byte offset for function declarations.
    pub fn inlay_hints_in(&self, start: usize, end: usize, text: &str) -> Vec<InlayHintData> {
        use crate::resolver::DefKind;

        let state = match self.state.as_ref() {
            Some(s) => s,
            None => return Vec::new(),
        };
        // One `TidyEnv` for every hint in this range so a tvar
        // shared by two bindings gets the same canonical ID — and
        // therefore the same letter — across hints. Each hint
        // still uses a fresh `PrettyContext`; that context's
        // letter-assignment state is no longer load-bearing
        // because tidy has already canonicalised the IDs.
        let mut tidy = inty::types::TidyEnv::new();
        let mut hints = Vec::new();
        // Walk defs in source order so the tidy env assigns IDs
        // in reading order — `defs_in_range` iterates a `HashMap`,
        // which would otherwise shuffle the ID-to-letter mapping
        // on every edit.
        let mut ordered: Vec<(Span, &crate::resolver::Def)> =
            self.resolution.defs_in_range(start, end).collect();
        ordered.sort_by_key(|(s, _)| (s.start, s.end));
        for (def_span, def) in ordered {
            if matches!(def.kind, DefKind::Catch | DefKind::Import) {
                continue;
            }
            // Don't hint on synthesised destructuring temps (their
            // names start with `$destr$` or `$param$N`).
            if def.name.starts_with('$') {
                continue;
            }
            let ty = match state.get_decl_type(def_span) {
                Some(t) => t,
                None => continue,
            };
            let applied = state.display_type_in(&mut tidy, ty);

            if matches!(def.kind, DefKind::Function) {
                // Function decls show only the return type, anchored
                // after `)`, instead of repeating the whole signature
                // after the function's name.
                if let Some((_, _, ret)) = applied.as_callable() {
                    if let Some(pos) = close_paren_after(text, def_span.end) {
                        let where_clause = where_clause_for(state, def_span, &mut tidy);
                        hints.push(InlayHintData {
                            after_byte: pos,
                            label: format!(" -> {}{}", format_type(ret.clone()), where_clause),
                        });
                    }
                }
                continue;
            }

            let where_clause = where_clause_for(state, def_span, &mut tidy);
            hints.push(InlayHintData {
                after_byte: def_span.end,
                label: format!(": {}{}", format_type(applied), where_clause),
            });
        }
        hints
    }
}

/// Inlay-hint payload returned by [`Analysis::inlay_hints_in`]. The
/// `label` already contains the leading `:` or `->`, so callers render
/// it verbatim.
pub struct InlayHintData {
    pub after_byte: usize,
    pub label: String,
}

/// If the binding at `def_span` was generalised with predicates,
/// return ` where ...` tidied into the shared `tidy` env so the
/// letters in the where-clause line up with the body's letters in
/// the same hint and with every other hint built from the same
/// env. Empty string when there's no scheme or no predicates.
fn where_clause_for(
    state: &InferState,
    def_span: Span,
    tidy: &mut inty::types::TidyEnv,
) -> String {
    let Some(scheme) = state.get_decl_scheme(def_span) else {
        return String::new();
    };
    let displayed = state.display_scheme_in(tidy, scheme);
    if displayed.body.preds.is_empty() {
        return String::new();
    }
    let mut ctx = PrettyContext::new();
    format!(" where {}", ctx.format_preds(&displayed.body.preds))
}

/// Format a tidied `Type` with a fresh `PrettyContext`. The context's
/// letter map is per-call because the input is already canonical —
/// see [`inty::types::TidyEnv`].
fn format_type(ty: Type) -> String {
    let mut ctx = PrettyContext::new();
    ctx.format_type(&ty)
}

/// Format a tidied `TypeScheme` with a fresh `PrettyContext`.
fn format_scheme(scheme: inty::types::TypeScheme) -> String {
    let mut ctx = PrettyContext::new();
    ctx.format_scheme(&scheme)
}

/// Starting at `name_end`, skip whitespace, then walk a balanced
/// parenthesised group and return the byte offset just past the
/// closing `)`. Returns `None` if no `(` follows the name. Strings
/// inside the param list are skipped so a literal `)` in a default
/// value doesn't fool the depth counter.
fn close_paren_after(text: &str, name_end: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut i = name_end;
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    if i >= bytes.len() || bytes[i] != b'(' {
        return None;
    }
    i += 1;
    let mut depth: usize = 1;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i + 1);
                }
            }
            q @ (b'"' | b'\'') => {
                i += 1;
                while i < bytes.len() && bytes[i] != q {
                    if bytes[i] == b'\\' && i + 1 < bytes.len() {
                        i += 1;
                    }
                    i += 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// One import specifier, decoded enough that the LSP rename logic can
/// reason about cross-file edits.
#[derive(Debug, Clone)]
pub struct ImportRecord {
    /// The module-path string from `from "..."`.
    pub source: String,
    /// The original (exported) name, or "default" / "*" for default
    /// and namespace imports respectively.
    pub imported: String,
    /// The local name introduced into this file.
    pub local: String,
    /// Source span of the local binding (this is what the resolver
    /// already records as a `DefKind::Import` def).
    pub local_span: Span,
    /// Source span of the *imported* name, for Named imports. For
    /// Default and Namespace this equals `local_span`.
    pub imported_span: Span,
    pub kind: ImportKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportKind {
    Named,
    Default,
    Namespace,
}

impl Analysis {
    /// Enumerate all `import` statements in the program. Used by
    /// cross-file rename to find which other open documents
    /// reference a binding being renamed in this document.
    pub fn imports(&self) -> Vec<ImportRecord> {
        let program = match self.program.as_ref() {
            Some(p) => p,
            None => return Vec::new(),
        };
        let mut out = Vec::new();
        for stmt in &program.statements {
            if let Stmt::Import {
                specifiers, source, ..
            } = stmt
            {
                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Named {
                            imported,
                            local,
                            span,
                        } => {
                            // The imported name starts at the spec
                            // span's start. For `foo as bar` that's
                            // `foo`; for `foo` it's `foo` (and equals
                            // the local).
                            let imported_span = Span::new(span.start, span.start + imported.len());
                            // The local name spans the whole specifier
                            // — the resolver also keys off `span` for
                            // `DefKind::Import`. For a non-aliased
                            // import the local *is* the imported.
                            let local_span = if imported == local {
                                imported_span
                            } else {
                                // Aliased: scan from the imported's
                                // end forward past whitespace and
                                // `as` to the local name.
                                local_span_from_aliased(
                                    self.source_text_unchecked(),
                                    *span,
                                    imported.len(),
                                    local.len(),
                                )
                            };
                            out.push(ImportRecord {
                                source: source.clone(),
                                imported: imported.clone(),
                                local: local.clone(),
                                local_span,
                                imported_span,
                                kind: ImportKind::Named,
                            });
                        }
                        ImportSpecifier::Default { local, span } => {
                            out.push(ImportRecord {
                                source: source.clone(),
                                imported: "default".to_string(),
                                local: local.clone(),
                                local_span: *span,
                                imported_span: *span,
                                kind: ImportKind::Default,
                            });
                        }
                        ImportSpecifier::Namespace { local, span } => {
                            out.push(ImportRecord {
                                source: source.clone(),
                                imported: "*".to_string(),
                                local: local.clone(),
                                local_span: *span,
                                imported_span: *span,
                                kind: ImportKind::Namespace,
                            });
                        }
                    }
                }
            }
        }
        out
    }

    fn source_text_unchecked(&self) -> &str {
        // The Analysis doesn't carry the source text directly. We
        // store it on Document at the server layer; for the import
        // span calculation we only need to rescan a small substring
        // by index, but that requires text access. Rather than thread
        // it everywhere, the local_span computation accepts the parser
        // span and trusts that our parser puts `as` between the names
        // — see local_span_from_aliased.
        ""
    }
}

/// Best-effort recovery of the local-name span in `{ imported as local }`
/// form when only the whole-specifier span is available. We can't see
/// the source here, so we synthesise a span sized to `local.len()` at
/// the *end* of the specifier — good enough for editors that highlight
/// rename ranges (the actual edit text is what matters).
fn local_span_from_aliased(
    _text: &str,
    spec_span: Span,
    _imported_len: usize,
    local_len: usize,
) -> Span {
    // Anchor at the end of the spec span: spec_span.end - local_len .. spec_span.end.
    // For a malformed span we fall back to the whole spec.
    if spec_span.end >= local_len + spec_span.start {
        Span::new(spec_span.end - local_len, spec_span.end)
    } else {
        spec_span
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

/// Pull the parameter list and return type out of a function type
/// (either bare `Type::Func` or a callable row carrying a `<CALL>`
/// field). `apply_subst` should already have been called on `ty`.
fn func_params(ty: &Type) -> Option<(Vec<Type>, Type)> {
    let (_, params, ret) = ty.as_callable()?;
    // Drop presence info here — the LSP's signature help only
    // surfaces the parameter types as a flat list. Optional params
    // still appear in the list; the optional `?` marker is
    // formatted into the type's display string by `PrettyContext`.
    Some((params.iter().map(|p| p.ty.clone()).collect(), ret.clone()))
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
        Stmt::If {
            test,
            consequent,
            alternate,
            ..
        } => {
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
        Stmt::Return {
            argument: Some(e), ..
        }
        | Stmt::Throw { argument: e, .. } => {
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
        Expr::Call {
            callee, arguments, ..
        }
        | Expr::New {
            callee, arguments, ..
        } => {
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
        Expr::ComputedMember {
            object, property, ..
        } => {
            find_call_expr(object, offset, best);
            find_call_expr(property, offset, best);
        }
        Expr::Conditional {
            test,
            consequent,
            alternate,
            ..
        } => {
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
/// Recursively resolve the type of a call's callee expression.
/// Supported shapes:
///
/// - `Expr::Ident { name }` — looked up in the env directly.
/// - `Expr::Member { object, property }` — recurses on `object`,
///   expects the result to be a row, picks `property` from the row's
///   props. Handles arbitrary chains (`a.b.c.method`).
///
/// Anything else (computed member, call returning a function, etc.)
/// returns `None` and the LSP server reports no signature help.
fn resolve_callee_type(env: &TypeEnv, state: &InferState, expr: &Expr) -> Option<(String, Type)> {
    use inty::types::PropName;
    match expr {
        Expr::Ident { name, .. } => {
            let scheme = env.lookup(name)?;
            let ty = state.flatten_type(&scheme.body.ty);
            Some((name.clone(), ty))
        }
        Expr::Member {
            object, property, ..
        } => {
            let (obj_label, obj_ty) = resolve_callee_type(env, state, object)?;
            let row = match &obj_ty {
                Type::Row(r) => r,
                _ => return None,
            };
            let entry = row.props.get(&PropName(property.clone()))?;
            let applied = state.flatten_type(&entry.ty);
            Some((format!("{}.{}", obj_label, property), applied))
        }
        _ => None,
    }
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
                use inty::ast::ForInit;
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
        Stmt::FunctionDecl {
            name, body, span, ..
        } => {
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
            use inty::ast::PropDef;
            for p in properties {
                match p {
                    PropDef::Property { value, .. } => visit_expr(value, offset, best),
                    PropDef::Method { body, .. }
                    | PropDef::Getter { body, .. }
                    | PropDef::Setter { body, .. } => visit_stmt(body, offset, best),
                    PropDef::Spread { argument, .. } => visit_expr(argument, offset, best),
                }
            }
        }
        Expr::Member { object, .. } => visit_expr(object, offset, best),
        Expr::ComputedMember {
            object, property, ..
        } => {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// `Analysis::check` is the entry point both the LSP server and the
    /// wasm playground use. If aliases aren't collected from the scanner
    /// here, every doc-comment `type Foo = ...` is silently dropped and
    /// references to `Foo` degrade to a fresh type variable — programs
    /// that should error type-check successfully.
    #[test]
    fn check_collects_type_aliases() {
        let src = "\
/** type Func = () => {id: String} */
/** const func: Func */
const func = function() { return {id: '123', name: 'hello'}; };";
        let analysis = Analysis::check(src);
        assert!(
            !analysis.errors.is_empty(),
            "expected excess-field rejection through nullary alias expansion, got {:?}",
            analysis.errors
        );
    }

    /// `Analysis::check` must drain every diagnostic the inference
    /// recovery path accumulated, not just the first. The LSP turns
    /// each into a squiggly; if we returned only one, the user would
    /// fix-recompile-fix-recompile in a loop.
    #[test]
    fn check_returns_every_accumulated_error() {
        let src = "var a = missingOne; var b = missingTwo; var c = missingThree;";
        let analysis = Analysis::check(src);
        let undef_count = analysis
            .errors
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    IntyError::Type(inty::error::TypeError::UndefinedVariable { .. })
                )
            })
            .count();
        assert!(
            undef_count >= 3,
            "expected three UndefinedVariable diagnostics, got {}: {:?}",
            undef_count,
            analysis.errors
        );
    }

    /// `check_lang` routes to the right frontend: a Lua document parses
    /// and type-checks, and a Lua type error surfaces as a diagnostic.
    #[test]
    fn check_lang_dispatches_to_lua() {
        let ok = Analysis::check_lang(
            "local function add(a, b) return a + b end\nlocal n = add(1, 2)",
            Language::Lua,
        );
        assert!(ok.errors.is_empty(), "expected ok, got {:?}", ok.errors);

        let bad = Analysis::check_lang("local x = 1 + \"oops\"", Language::Lua);
        assert!(!bad.errors.is_empty(), "expected a type error");
    }

    /// Likewise for Python, including indentation-driven blocks.
    #[test]
    fn check_lang_dispatches_to_python() {
        let ok = Analysis::check_lang(
            "def add(a, b):\n    return a + b\n\nn = add(1, 2)\n",
            Language::Python,
        );
        assert!(ok.errors.is_empty(), "expected ok, got {:?}", ok.errors);

        let bad = Analysis::check_lang("x = 1 + \"oops\"\n", Language::Python);
        assert!(!bad.errors.is_empty(), "expected a type error");
    }
}
