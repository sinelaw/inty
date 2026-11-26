//! Run inty's lex/parse/infer pipeline on an in-memory document and
//! expose the results in a form the LSP server can query.

use lsp_types::{CompletionItem, CompletionItemKind};

use inty::ast::visit::each_expr;
use inty::ast::{Expr, ImportSpecifier, Program, Stmt};
use inty::error::IntyError;
use inty::frontends::Language;
use inty::infer::{InferState, InferWarning, TypeEnv};
use inty::span::Span;
use inty::stdlib::initial_env_with_stdlib;
use inty::types::{PrettyContext, RowType, Type};

use crate::resolver::Resolution;

/// Result of checking one document: the errors found and (when the
/// program parsed) the inference state needed to answer hover queries.
pub struct Analysis {
    pub errors: Vec<IntyError>,
    /// The document as checked: hover reads the word under the cursor
    /// off it.
    text: String,
    program: Option<Program>,
    final_env: Option<TypeEnv>,
    state: Option<InferState>,
    pub resolution: Resolution,
    /// How the document's types are shown, built once from the check
    /// (see [`Presentation`]): every hint and hover prints through it.
    presentation: std::cell::OnceCell<Presentation>,
}

impl Analysis {
    /// Lex, parse, and infer `text` as JavaScript. Always returns an
    /// `Analysis`; on any error the relevant fields are left empty.
    pub fn check(text: &str) -> Self {
        Self::check_lang(text, Language::JavaScript)
    }

    /// Like [`Analysis::check`], but for an explicit frontend.
    pub fn check_lang(text: &str, lang: Language) -> Self {
        Self::check_document(text, lang, None)
    }

    /// Check `text`, the contents of the document at `path` (`None` for
    /// one with no file), as the CLI checks that file: with its
    /// language's prelude and what it imports (read from disk, relative
    /// to `path`). Only this document's own errors and warnings are
    /// kept; an imported module's are its own document's.
    pub fn check_document(text: &str, lang: Language, path: Option<&std::path::Path>) -> Self {
        let mut errors = Vec::new();

        // Parse through the same entry point as the CLI, so the editor
        // sees exactly the program the checker does (for JavaScript:
        // JSDoc annotations and aliases, and the source text the
        // parser's ASI and inline-annotation rules read).
        let program = match inty::frontends::parse(lang, text) {
            Ok(p) => p,
            Err(e) => {
                errors.push(e);
                return Analysis::errors_only(text, errors);
            }
        };

        // Resolve identifiers (independent of type inference). We pass
        // the text length so the module scope covers EOF — otherwise
        // queries past the last statement (a blank line at the end of
        // the file) would find no scope.
        let resolution = Resolution::build_with_len(&program, text.len());

        // The environment the CLI checks the file in: the embedded
        // stdlib, the language's prelude, and the file's imports.
        let env_state = initial_env_with_stdlib().and_then(|(base, mut state)| {
            let env = inty::frontends::program_env(&mut state, base, &program, lang, path)
                .map_err(|e| this_document(e, state.current_source()))?;
            Ok((env, state))
        });
        let (env, mut state) = match env_state {
            Ok(r) => r,
            Err(e) => {
                errors.push(e);
                return Analysis {
                    errors,
                    text: text.to_string(),
                    program: Some(program),
                    final_env: None,
                    state: None,
                    resolution,
                    presentation: Default::default(),
                };
            }
        };

        // Infer. The `Type::Error` recovery path lets inference
        // continue past a failing statement, so `state.errors` may
        // contain multiple diagnostics even though the public API
        // only returns the first via `Result::Err`. Drain the
        // accumulated list so every diagnostic surfaces as an LSP
        // squiggly, not just the first.
        // Every expression's type, for hover on a member's property
        // (`s.startsWith`). Only this document's: its imports are checked.
        state.expr_types = Some(Default::default());
        let infer_result = state.infer_program_with_env(&env, &program);
        let collected: Vec<IntyError> = state
            .take_located_errors()
            .into_iter()
            .filter(|e| e.source.is_none())
            .map(|e| e.error)
            .collect();
        match infer_result {
            Ok((_ty, final_env)) => {
                if let Err(e) = state.resolve_constraints() {
                    errors.push(e);
                }
                errors.extend(collected);
                Analysis {
                    errors,
                    text: text.to_string(),
                    program: Some(program),
                    final_env: Some(final_env),
                    state: Some(state),
                    resolution,
                    presentation: Default::default(),
                }
            }
            Err(_first) => {
                // `_first` is the head of `collected`; use the
                // accumulated list as-is to avoid duplicating it.
                errors.extend(collected);
                // Recovery still typed every statement that didn't
                // fail: keep that env so hover, completion, and
                // signature help work in a file with a type error.
                let final_env = state.take_env_after_errors();
                Analysis {
                    errors,
                    text: text.to_string(),
                    program: Some(program),
                    final_env,
                    state: Some(state),
                    resolution,
                    presentation: Default::default(),
                }
            }
        }
    }

    /// Non-fatal warnings collected during inference (e.g. unreachable
    /// narrowing branches). Empty if inference didn't run or didn't emit
    /// any.
    pub fn warnings(&self) -> Vec<&InferWarning> {
        match self.state.as_ref() {
            // An imported module's spans are its own file's.
            Some(s) => s
                .warnings
                .iter()
                .filter(|w| s.sources.locate(w.span).is_none())
                .collect(),
            None => Vec::new(),
        }
    }

    fn errors_only(text: &str, errors: Vec<IntyError>) -> Self {
        Analysis {
            errors,
            text: text.to_string(),
            program: None,
            final_env: None,
            state: None,
            resolution: Resolution::default(),
            presentation: Default::default(),
        }
    }

    /// The type at `byte_offset`, as inference recorded it, for the word
    /// there:
    ///
    /// 1. A name the resolver knows (a declaration, or a use of one)
    ///    shows its declaration's type: the scheme a generic function
    ///    has (`<a>(a) => a`), shadow-correct.
    /// 2. Anything else shows the type inference recorded
    ///    (`expr_types`) for the innermost expression the word begins
    ///    or ends: itself (a global, `this`), a member it is the
    ///    property of (`s.startsWith`), one it is the keyword of
    ///    (`new Map()`); or a literal it is inside (`"#prompt"`). An
    ///    expression the front end made up (a class field's `$field$N`,
    ///    in place of `this.x`) isn't one the source shows, so it
    ///    doesn't count.
    ///
    /// Hover computes no type of its own, so what inference types,
    /// hover shows. Off any word, nothing.
    pub fn hover_at(&self, byte_offset: usize) -> Option<HoverResult> {
        let state = self.state.as_ref()?;
        let word = word_at(&self.text, byte_offset)?;
        let name = self.text[word.start..word.end].to_string();

        // A name the source shows where the resolver has it: not one the
        // front end made up (a class's field, `this.x = …`, is a
        // `$field$N` declared there).
        let named = self
            .resolution
            .binding_at(word.start)
            .and_then(|(def_span, hit_span)| {
                Some((self.resolution.def_at(def_span)?, def_span, hit_span))
            })
            .filter(|(def, _, hit_span)| {
                self.text.get(hit_span.start..hit_span.end) == Some(def.name.as_str())
            });
        if let Some((def, def_span, hit_span)) = named {
            // As its hint shows it, the constraints its type reaches
            // added.
            let ty = state.get_decl_type(def_span).cloned().or_else(|| {
                // A binding inference keys by name alone (a catch
                // parameter).
                let env = self.final_env.as_ref()?;
                env.lookup(&def.name).map(|scheme| scheme.body.ty.clone())
            });
            if let Some(ty) = ty {
                return Some(HoverResult {
                    name: def.name.clone(),
                    span: hit_span,
                    type_str: self.describe_at(word.start, &ty, state.get_decl_scheme(def_span)),
                });
            }
        }

        let mut made_up = std::collections::HashSet::new();
        let mut literals = std::collections::HashSet::new();
        each_expr(&self.program.as_ref()?.statements, &mut |e| match e {
            Expr::Ident { name, span } => {
                if self.text.get(span.start..span.end) != Some(name.as_str()) {
                    made_up.insert((span.start, span.end));
                }
            }
            Expr::Lit { span, .. } | Expr::TemplateLiteral { span, .. } => {
                literals.insert((span.start, span.end));
            }
            _ => {}
        });
        let (_, ty) = state
            .expr_types
            .as_ref()?
            .iter()
            .filter(|(&(start, end), _)| {
                let holds = start <= word.start && word.end <= end;
                let bounds = start == word.start || end == word.end;
                holds
                    && (bounds || literals.contains(&(start, end)))
                    && !made_up.contains(&(start, end))
            })
            .min_by_key(|((start, end), _)| (end - start, *start))?;
        let ty = ty.clone();
        Some(HoverResult {
            name,
            span: word,
            type_str: self.describe_at(word.start, &ty, None),
        })
    }

    /// The presentation, built on first use.
    fn presentation(&self) -> &Presentation {
        self.presentation.get_or_init(|| Presentation::build(self))
    }

    /// `ty` as hover shows it at `offset`: in the naming of the scope
    /// there (so as its hints name its variables), with every
    /// constraint it reaches — its own scheme's (`own`), and those of
    /// the schemes around it (a local's type variables are constrained
    /// by its enclosing function's).
    fn describe_at(
        &self,
        offset: usize,
        ty: &Type,
        own: Option<&inty::types::TypeScheme>,
    ) -> String {
        let Some(state) = self.state.as_ref() else {
            return String::new();
        };
        let presentation = self.presentation();
        let scope = presentation.scope_at(offset);
        let mut tidy = scope.map(|s| s.tidy.clone()).unwrap_or_default();
        let pool = scope.map(|s| s.pool.as_slice()).unwrap_or(&[]);
        let (ty, where_clause) = describe(state, &mut tidy, ty, own, pool);
        format!("{ty}{where_clause}")
    }

    /// Format the type of `name` (looked up in the final env) as a
    /// short string, for use as completion-item `detail`. Returns
    /// `None` if the name isn't visible.
    pub fn type_of_name(&self, name: &str) -> Option<String> {
        let env = self.final_env.as_ref()?;
        let state = self.state.as_ref()?;
        let scheme = env.lookup(name)?;
        Some(format_scheme(state, state.display_scheme(scheme)))
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
                detail: Some(format_type(state, entry.ty.clone())),
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

        let param_labels: Vec<String> = params
            .iter()
            .map(|p| format_type(state, p.clone()))
            .collect();
        let ret_label = format_type(state, ret.clone());
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
    /// The hints are the document's, built once (see
    /// [`Presentation`]): which are asked for doesn't change what any
    /// of them says.
    pub fn inlay_hints_in(&self, start: usize, end: usize) -> Vec<InlayHintData> {
        self.presentation()
            .scopes
            .iter()
            .flat_map(|scope| &scope.hints)
            .filter(|(def_span, _)| start <= def_span.start && def_span.start < end)
            .map(|(_, hint)| hint.clone())
            .collect()
    }
}

/// How a document's types are shown: one naming of type variables per
/// top-level statement (a function and everything in it), assigned in
/// reading order, which every hint and hover in it prints with. Built
/// once from the check, so what is shown doesn't depend on what is asked
/// for first, or which part of the document is in view.
#[derive(Default)]
struct Presentation {
    scopes: Vec<Scope>,
}

/// One top-level statement's naming, its hints, and the constraints of
/// every scheme in it (what a local's type variables are constrained by).
struct Scope {
    span: Span,
    tidy: inty::types::TidyEnv,
    hints: Vec<(Span, InlayHintData)>,
    pool: Vec<inty::types::TypePred>,
}

impl Presentation {
    fn build(analysis: &Analysis) -> Presentation {
        let (Some(state), Some(program)) = (analysis.state.as_ref(), analysis.program.as_ref())
        else {
            return Presentation::default();
        };
        // A binding is its first scope's: a front end can lower one
        // source statement to several whose spans overlap (a Python
        // tuple assignment).
        let mut claimed = std::collections::HashSet::new();
        let scopes = program
            .statements
            .iter()
            .map(|stmt| {
                let span = stmt.span();
                Scope::build(
                    analysis,
                    state,
                    Span::new(span.start, span.end),
                    &mut claimed,
                )
            })
            .collect();
        Presentation { scopes }
    }

    fn scope_at(&self, offset: usize) -> Option<&Scope> {
        self.scopes
            .iter()
            .find(|s| s.span.start <= offset && offset <= s.span.end)
    }
}

impl Scope {
    fn build(
        analysis: &Analysis,
        state: &InferState,
        span: Span,
        claimed: &mut std::collections::HashSet<(usize, usize)>,
    ) -> Scope {
        use crate::resolver::DefKind;
        let text = analysis.text.as_str();
        let mut tidy = inty::types::TidyEnv::new();
        let mut hints = Vec::new();
        let mut pool = Vec::new();
        // In source order, so names are assigned in reading order
        // (`defs_in_range` iterates a `HashMap`).
        let mut ordered: Vec<(Span, &crate::resolver::Def)> = analysis
            .resolution
            .defs_in_range(span.start, span.end)
            .filter(|(s, _)| claimed.insert((s.start, s.end)))
            .collect();
        ordered.sort_by_key(|(s, _)| (s.start, s.end));
        for (def_span, def) in ordered {
            if let Some(scheme) = state.get_decl_scheme(def_span) {
                pool.extend(state.flatten_scheme(scheme).body.preds);
            }
            if matches!(def.kind, DefKind::Catch | DefKind::Import) {
                continue;
            }
            // Don't hint on synthesised destructuring temps (their
            // names start with `$destr$` or `$param$N`).
            if def.name.starts_with('$') {
                continue;
            }
            let Some(ty) = state.get_decl_type(def_span) else {
                continue;
            };
            let scheme = state.get_decl_scheme(def_span);
            let (shown, where_clause) = describe(state, &mut tidy, ty, scheme, &[]);

            if matches!(def.kind, DefKind::Function) {
                // Function decls show only the return type, anchored
                // after `)`, instead of repeating the whole signature
                // after the function's name. A declared return type
                // (`def f() -> int`) already says it.
                // A Python `class C():` lowers to a factory function;
                // its "return type" is the instance, not worth a hint.
                if def.annotated
                    || text[..def_span.start.min(text.len())]
                        .trim_end()
                        .ends_with("class")
                {
                    continue;
                }
                let applied = state.display_type_in(&mut tidy, ty);
                if let Some((_, _, ret)) = applied.as_callable() {
                    if let Some(pos) = close_paren_after(text, def_span.end) {
                        hints.push((
                            def_span,
                            InlayHintData {
                                after_byte: pos,
                                label: format!(
                                    " -> {}{}",
                                    format_hint(state, ret.clone()),
                                    where_clause
                                ),
                            },
                        ));
                    }
                }
                continue;
            }

            // Inference gave up on this binding (an error was reported
            // where it failed); `x: <error>` adds nothing to that.
            if shown == "<error>" {
                continue;
            }
            // The source states its type (`x: int`, `/** const x: T */`,
            // its function's `/** function f(x: T) => R */`).
            if def.annotated {
                continue;
            }
            hints.push((
                def_span,
                InlayHintData {
                    after_byte: def_span.end,
                    label: format!(": {shown}{where_clause}"),
                },
            ));
        }
        Scope {
            span,
            tidy,
            hints,
            pool,
        }
    }
}

/// `ty` printed in the naming `tidy` holds (assigning names to any
/// variable it hasn't named yet), and its ` where …` clause: `own`'s
/// constraints (a generalised binding's scheme), and, from `pool`, every
/// constraint `ty` or those reach through its subject (see
/// [`inty::types::ClassName::subject_positions`]). Every hint and hover
/// prints through here, so a type reads the same wherever it is shown.
fn describe(
    state: &InferState,
    tidy: &mut inty::types::TidyEnv,
    ty: &Type,
    own: Option<&inty::types::TypeScheme>,
    pool: &[inty::types::TypePred],
) -> (String, String) {
    let ty = state.flatten_type(ty);
    let (quantified, mut preds) = own
        .map(|scheme| {
            let flat = state.flatten_scheme(scheme);
            (flat.vars, flat.body.preds)
        })
        .unwrap_or_default();
    let mut reached = ty.free_vars();
    for p in &preds {
        for t in &p.types {
            reached.extend(t.free_vars());
        }
    }
    let mut taken = vec![false; pool.len()];
    loop {
        let mut changed = false;
        for (i, pred) in pool.iter().enumerate() {
            if taken[i] {
                continue;
            }
            let reaches =
                pred.class
                    .subject_positions(pred.types.len())
                    .iter()
                    .any(|&k| match &pred.types[k] {
                        Type::Var(v) => reached.contains(v),
                        _ => false,
                    });
            if reaches {
                taken[i] = true;
                changed = true;
                for t in &pred.types {
                    reached.extend(t.free_vars());
                }
                if !preds.contains(pred) {
                    preds.push(pred.clone());
                }
            }
        }
        if !changed {
            break;
        }
    }
    // The type's variables are named first, in reading order
    // (`(items: a, q: b) => c`), then its constraints'.
    tidy.tidy_type(&ty);
    let displayed = tidy.tidy_scheme(&inty::types::TypeScheme {
        vars: quantified,
        pvars: Vec::new(),
        body: inty::types::QualType { preds, ty },
    });
    // A generalised binding's own variables, as `<a, b>`: those it
    // doesn't quantify are an enclosing scope's.
    let mut ctx = pretty_context(state, &displayed.body.ty).hiding_row_args();
    let mentioned = inty::types::displayed_vars_of_scheme(&displayed);
    let own_vars: Vec<String> = displayed
        .vars
        .iter()
        .filter(|v| mentioned.contains(*v))
        .map(|v| ctx.format_type(&Type::Var(v.clone())))
        .collect();
    let prefix = if own_vars.is_empty() {
        String::new()
    } else {
        format!("<{}>", own_vars.join(", "))
    };
    let shown = format!("{prefix}{}", ctx.format_type(&displayed.body.ty));
    let preds: Vec<_> = displayed
        .body
        .preds
        .into_iter()
        .filter(|p| !is_vacuous_inject(p))
        .collect();
    let where_clause = if preds.is_empty() {
        String::new()
    } else {
        format!(" where {}", ctx.format_preds(&preds))
    };
    (shown, where_clause)
}

/// Inlay-hint payload returned by [`Analysis::inlay_hints_in`]. The
/// `label` already contains the leading `:` or `->`, so callers render
/// it verbatim.
#[derive(Clone)]
pub struct InlayHintData {
    pub after_byte: usize,
    pub label: String,
}

/// `Inject a (Null | a)`: `a` is accepted where `Null | a` is, which
/// holds by construction — `a` is one of the arms. Says nothing to a
/// reader, so hints leave it out.
fn is_vacuous_inject(pred: &inty::types::TypePred) -> bool {
    if pred.class != inty::types::ClassName::Inject || pred.types.len() != 2 {
        return false;
    }
    let (sub, sup) = (&pred.types[0], &pred.types[1]);
    match sup {
        Type::Maybe(_, inner) => **inner == *sub,
        Type::Union(arms) => arms.contains(sub),
        _ => false,
    }
}

/// A fresh `PrettyContext` for printing `ty`: the one diagnostics use
/// ([`InferState::printer`]), so classes, brands and aliases print by
/// their declared names (`Counter`, `PaletteItem`). Anonymous recursive
/// types have no name: a reference back to the object `ty` itself prints
/// as `Self` (`setUrl: (this: Self, String) => Self`), any other as `{…}`.
fn pretty_context(state: &InferState, ty: &Type) -> PrettyContext {
    let mut ctx = state.printer();
    let own_fields = match ty {
        Type::Row(row) => Some(row.props.keys().collect::<Vec<_>>()),
        _ => None,
    };
    for id in ty.named_ids() {
        let Some(def) = state.get_named_type(id) else {
            continue;
        };
        if def.name.is_some() {
            continue;
        }
        let is_self = match (&own_fields, &def.body) {
            (Some(own), Type::Row(body)) => body.props.keys().collect::<Vec<_>>() == *own,
            _ => false,
        };
        ctx = ctx.naming(id, if is_self { "Self" } else { "{…}" }.to_string());
    }
    ctx
}

/// Format a tidied `Type` with a fresh `PrettyContext`. The context's
/// letter map is per-call because the input is already canonical —
/// see [`inty::types::TidyEnv`].
fn format_type(state: &InferState, ty: Type) -> String {
    pretty_context(state, &ty).format_type(&ty)
}

/// Format a tidied `Type` for an inlay hint, which sits inline in the
/// code and so drops detail hover keeps (a class's field-row argument).
fn format_hint(state: &InferState, ty: Type) -> String {
    pretty_context(state, &ty)
        .hiding_row_args()
        .format_type(&ty)
}

/// Format a tidied `TypeScheme` with a fresh `PrettyContext`.
fn format_scheme(state: &InferState, scheme: inty::types::TypeScheme) -> String {
    pretty_context(state, &scheme.body.ty).format_scheme(&scheme)
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
        for (_, v) in expr.keyword_args() {
            find_call_expr(v, offset, best);
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
    for &b in bytes.get(start..end).unwrap_or(&[]) {
        match b {
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
/// An error for this document: as it is when raised here (`source`
/// `None`); raised in another file (an imported module that couldn't be
/// loaded), named with that file and placed at the document's start.
fn this_document(error: IntyError, source: Option<inty::error::SourceFile>) -> IntyError {
    match source {
        None => error,
        Some(file) => inty::error::TypeError::Module {
            message: format!("in {}: {}", file.path, error),
            span: Span::new(0, 0),
        }
        .into(),
    }
}

fn span_contains(span: Span, offset: usize) -> bool {
    span.start <= offset && offset <= span.end
}

/// The word (identifier, keyword, or number) at `offset`, or just
/// before it (a cursor right after a word); `None` off any word.
fn word_at(text: &str, offset: usize) -> Option<Span> {
    let is_word = |c: char| c.is_alphanumeric() || c == '_' || c == '$';
    let offset = offset.min(text.len());
    let at = |i: usize| text.get(i..).and_then(|t| t.chars().next());
    let mut start = if at(offset).is_some_and(is_word) {
        offset
    } else {
        let (i, c) = text.get(..offset)?.char_indices().next_back()?;
        if !is_word(c) {
            return None;
        }
        i
    };
    while let Some((i, c)) = text[..start].char_indices().next_back() {
        if !is_word(c) {
            break;
        }
        start = i;
    }
    let end = text[start..]
        .char_indices()
        .find(|&(_, c)| !is_word(c))
        .map_or(text.len(), |(i, _)| start + i);
    Some(Span::new(start, end))
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
                    e.as_type(),
                    Some(inty::error::TypeError::UndefinedVariable { .. })
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

    /// A type error in one statement must not blind the editor to the
    /// rest of the file: inference recovers past it, so hover,
    /// completion details, and member completion still answer for the
    /// bindings that typed fine — before and after the error.
    #[test]
    fn queries_answer_in_a_file_with_a_type_error() {
        let src = "const n = 1;\nconst bad = n + 'a' - {};\nconst o = {x: 1, y: 'two'};\n";
        let analysis = Analysis::check(src);
        assert!(!analysis.errors.is_empty(), "expected the type error");

        let hover = analysis
            .hover_at(src.find("n =").unwrap())
            .expect("hover on `n`");
        assert_eq!(
            (hover.name.as_str(), hover.type_str.as_str()),
            ("n", "Number")
        );
        let hover = analysis
            .hover_at(src.find("o =").unwrap())
            .expect("hover on `o`");
        assert_eq!(hover.name, "o");

        assert_eq!(analysis.type_of_name("n").as_deref(), Some("Number"));

        let text = format!("{src}o.");
        let items = analysis
            .member_completions_before_with(&text, text.len())
            .expect("member completions on `o.`");
        let mut labels: Vec<_> = items.iter().map(|i| i.label.as_str()).collect();
        labels.sort();
        assert_eq!(labels, ["x", "y"]);
    }

    /// The name a declaration binds answers hover wherever the name
    /// sits: after `export`, `export async`, `class`, or Lua's `local`.
    #[test]
    fn hover_finds_each_declared_name() {
        let src = "export function f(a) { return a; }\n\
                   export async function g() { return 1; }\n\
                   class C { constructor() { this.n = 1; } }\n\
                   export class D { constructor() { this.s = ''; } }\n";
        let analysis = Analysis::check(src);
        assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
        for name in ["f", "g", "C", "D"] {
            let at = [format!(" {name}("), format!(" {name} {{")]
                .iter()
                .find_map(|needle| src.find(needle.as_str()))
                .unwrap()
                + 1;
            let hover = analysis
                .hover_at(at)
                .unwrap_or_else(|| panic!("hover on `{name}`"));
            assert_eq!(hover.name, name);
        }

        let src = "local function add(a, b) return a + b end\n";
        let analysis = Analysis::check_lang(src, Language::Lua);
        let hover = analysis
            .hover_at(src.find("add").unwrap())
            .expect("hover on `add`");
        assert_eq!(hover.name, "add");
    }

    /// The editor checks the program the CLI does: a `return` ends at
    /// its line's end (ASI), which the parser decides from the source.
    #[test]
    fn parses_the_program_the_cli_checks() {
        let src = "function f() {\n  return\n  1;\n}\n";
        let analysis = Analysis::check(src);
        let hover = analysis
            .hover_at(src.find("f(").unwrap())
            .expect("hover on `f`");
        assert_eq!(hover.type_str, "() => Undefined");
    }

    /// A type alias that doesn't parse is reported, and the rest of
    /// the file is still checked and answers hover.
    #[test]
    fn a_bad_type_alias_is_reported_and_the_rest_answers() {
        let src = "/** type S = { run: (String) => Item } */\nconst n = 1;\n";
        let analysis = Analysis::check(src);
        let shown: Vec<String> = analysis.errors.iter().map(|e| e.to_string()).collect();
        assert!(
            shown.iter().any(|e| e.contains("unknown type 'Item'")),
            "{shown:?}"
        );
        let hover = analysis
            .hover_at(src.find("n =").unwrap())
            .expect("hover on `n`");
        assert_eq!(hover.type_str, "Number");
    }

    /// Hover answers on a name, not on the rest of its declaration: off
    /// any name, in a function's body or a declarator's initialiser,
    /// there is nothing to show.
    #[test]
    fn hover_off_a_name_is_nothing() {
        let src = "function f(a) {  return a; }\nconst x =   1;\n";
        let analysis = Analysis::check(src);
        assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
        for (what, at) in [
            ("function body", src.find("{ ").unwrap() + 1),
            ("initialiser", src.find("=   ").unwrap() + 2),
        ] {
            let hover = analysis.hover_at(at).map(|h| h.name);
            assert_eq!(hover, None, "hover in the {what}");
        }
    }

    /// An annotation that doesn't parse is reported, and what it
    /// annotates is checked as if it had none: a function's parameters
    /// and locals, and a constant, still answer hover.
    #[test]
    fn a_bad_annotation_is_reported_and_its_declaration_checked() {
        let src = "/** function f(a: String) => Item */\n\
                   function f(a) { const z = a; return z; }\n\
                   /** const x: Item */\n\
                   const x = 1;\n";
        let analysis = Analysis::check(src);
        let shown: Vec<String> = analysis.errors.iter().map(|e| e.to_string()).collect();
        assert_eq!(shown.len(), 2, "{shown:?}");
        assert!(
            shown.iter().all(|e| e.contains("unknown type 'Item'")),
            "{shown:?}"
        );
        for (needle, name) in [("(a)", "a"), ("z =", "z"), ("x =", "x")] {
            let at = src.find(needle).unwrap() + needle.find(name).unwrap();
            let hover = analysis
                .hover_at(at)
                .unwrap_or_else(|| panic!("hover on `{name}`"));
            assert_eq!(hover.name, name);
        }
        let x = analysis.hover_at(src.find("x =").unwrap()).unwrap();
        assert_eq!(x.type_str, "Number");
    }

    /// A member's property answers hover with the member's type: a
    /// method (`s.startsWith`, typed where the call checks it), a field,
    /// each link of a chain, and one on a line of its own.
    #[test]
    fn hover_on_a_member_s_property() {
        let src = "const s = 'abc';\n\
                   const b = s.startsWith('a');\n\
                   const o = {a: {b: 'x'}};\n\
                   const n = o.a.b.length;\n\
                   const d = o\n  .a;\n";
        let analysis = Analysis::check(src);
        assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
        for (needle, name, ty) in [
            (
                "startsWith",
                "startsWith",
                "(this: String, String, Number?) => Boolean",
            ),
            ("a.b.length", "a", "{b: String}"),
            ("b.length", "b", "String"),
            ("length", "length", "Number"),
            ("a;", "a", "{b: String}"),
        ] {
            let hover = analysis
                .hover_at(src.find(needle).unwrap() + 1)
                .unwrap_or_else(|| panic!("hover on `{needle}`"));
            assert_eq!((hover.name.as_str(), hover.type_str.as_str()), (name, ty));
        }
    }

    /// Hover shows what inference recorded for the word under the
    /// cursor, whatever expression holds it: nothing in hover is typed
    /// by hand, so nothing inference types is missing from it.
    #[test]
    fn hover_shows_what_inference_recorded() {
        let src = "const o = {a: {b: 1}, m() { return this.a; }};\n\
                   const n = 42;\n\
                   const g = Math.max(1, 2);\n\
                   const m = new Map();\n\
                   const d = o?.a.b;\n";
        let analysis = Analysis::check(src);
        assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
        for (needle, name, ty) in [
            ("42", "42", "42"),
            (
                "this",
                "this",
                "{a: {b: Number}, m: (this: {…}) => {b: Number}}",
            ),
            ("max", "max", "(Number, Number) => Number"),
            ("new", "new", "Map<a, b>"),
            ("a.b;", "a", "{b: Number}"),
            ("b;", "b", "Number"),
        ] {
            let hover = analysis
                .hover_at(src.find(needle).unwrap() + 1)
                .unwrap_or_else(|| panic!("hover on `{needle}`"));
            assert_eq!((hover.name.as_str(), hover.type_str.as_str()), (name, ty));
        }
        let src_lit = "const p = '#prompt';\n";
        let lit = Analysis::check(src_lit);
        let hover = lit
            .hover_at(src_lit.find("prompt").unwrap() + 2)
            .expect("hover in a string");
        assert_eq!(hover.type_str, "\"#prompt\"");
        // Off any word: an operator after a space, whitespace.
        for off in [src.find("= 42").unwrap(), src.find("= 42").unwrap() + 1] {
            assert!(analysis.hover_at(off).is_none(), "hover at {off}");
        }

        let src = "n = len('ab')\ns = 'x'.upper()\n";
        let analysis = Analysis::check_lang(src, Language::Python);
        let hover = analysis
            .hover_at(src.find("upper").unwrap())
            .expect("hover on `upper`");
        assert_eq!(hover.type_str, "(String?) => String");
    }

    /// A name or expression the front end made up never shows: a class
    /// field set in the constructor (`this.el = e`) is a hidden local
    /// there, which the source doesn't show. What the source does show
    /// still answers.
    #[test]
    fn hover_never_shows_a_made_up_name() {
        let src =
            "class P {\n  constructor(e) {\n    this.el = e;\n  }\n  m() { return this.el; }\n}\n";
        let analysis = Analysis::check(src);
        assert!(analysis.errors.is_empty(), "{:?}", analysis.errors);
        for needle in ["this.el =", "el ="] {
            let hover = analysis.hover_at(src.find(needle).unwrap() + 1);
            assert!(
                hover
                    .as_ref()
                    .is_none_or(|h| !h.name.contains('$') && !h.type_str.contains('$')),
                "hover in `{needle}`: {:?}",
                hover.map(|h| (h.name, h.type_str))
            );
        }
        let e = analysis
            .hover_at(src.find("= e").unwrap() + 2)
            .expect("hover on `e`");
        assert_eq!(e.name, "e");
        let el = analysis
            .hover_at(src.find("el; }").unwrap())
            .expect("hover on `el` in `m`");
        assert_eq!(el.name, "el");
    }

    /// A type error in one method leaves the rest of the class checked:
    /// a later method's words answer hover.
    #[test]
    fn an_error_in_one_method_leaves_the_others_hoverable() {
        let src = "class P {\n\
                   \x20 constructor() { this.n = 1; }\n\
                   \x20 bad() { return 1 - {}; }\n\
                   \x20 good(d) { return this.n + d; }\n\
                   }\n";
        let analysis = Analysis::check(src);
        assert_eq!(analysis.errors.len(), 1, "{:?}", analysis.errors);
        let at = src.find("n + d").unwrap();
        let n = analysis.hover_at(at).expect("hover on `n` in `good`");
        assert_eq!((n.name.as_str(), n.type_str.as_str()), ("n", "Number"));
        let d = analysis.hover_at(at + 4).expect("hover on `d`");
        assert_eq!((d.name.as_str(), d.type_str.as_str()), ("d", "Number"));
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

    #[test]
    fn check_lang_dispatches_to_starlark() {
        // Loaded names are bound opaquely (no path to resolve labels);
        // Bazel's globals are in scope.
        let ok = Analysis::check_lang(
            "load(\"//lib:a.bzl\", \"helper\")\n\
             def _impl(ctx):\n    return [DefaultInfo(files = depset(helper(ctx)))]\n\
             my_rule = rule(implementation = _impl)\n\
             names = [s.upper() for s in [\"a\"]]\n",
            Language::Starlark,
        );
        assert!(ok.errors.is_empty(), "expected ok, got {:?}", ok.errors);

        let bad = Analysis::check_lang("x = 1 + \"oops\"\n", Language::Starlark);
        assert!(!bad.errors.is_empty(), "expected a type error");
        let not_starlark = Analysis::check_lang("class C:\n    pass\n", Language::Starlark);
        assert!(!not_starlark.errors.is_empty(), "expected a parse error");
    }
}
