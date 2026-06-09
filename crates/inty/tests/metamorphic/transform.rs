//! Semantics-preserving transformations on `Program` ASTs. Each returns
//! the transformed program together with a [`Comparison`] that describes
//! how the transformation renamed / introduced / removed bindings, so
//! the oracle can assert the appropriate equivalence.

use inty::ast::*;
use inty::span::Span;

use super::ast::{
    bound_names_in_stmt, empty_stmt, fresh_name, names_in, num_lit, referenced_names_in_stmt,
    rename_all, span, var_stmt,
};
use super::oracle::Comparison;

// -------------------------------------------------------------------------
// Trivial prefix/interspersing transformations.
// -------------------------------------------------------------------------

fn prepend_stmt(program: &Program, extra: Stmt) -> Program {
    let mut statements = Vec::with_capacity(program.statements.len() + 1);
    statements.push(extra);
    statements.extend(program.statements.iter().cloned());
    Program {
        statements,
        span: span(),
        type_aliases: Vec::new(),
        class_brands: Vec::new(),
        class_bases: Vec::new(),
        language: inty::ast::SourceLanguage::JavaScript,
    }
}

/// T: prepend `;`. The empty statement is a no-op at runtime and
/// contributes `Undefined` as a statement result, so adding one at the
/// start changes nothing about how subsequent statements infer.
pub fn t_prepend_empty(p: &Program) -> (Program, Comparison) {
    (prepend_stmt(p, empty_stmt()), Comparison::identity())
}

/// T: prepend `var <fresh> = 0;`. The new binding is globally fresh
/// relative to `p`, so nothing references it — inference shouldn't care.
/// The injected name is declared as `q_only` so the oracle skips it.
pub fn t_prepend_dead_var(p: &Program) -> (Program, Comparison) {
    let taken = names_in(p);
    let name = fresh_name("__metamorphic_dead_", &taken);
    let transformed = prepend_stmt(p, var_stmt(VarKind::Var, &name, Some(num_lit(0.0))));
    (transformed, Comparison::identity().with_q_only(vec![name]))
}

/// T: insert `;` between adjacent statements. An inserted empty
/// statement sets the running "program result" to `Undefined`; if
/// nothing *after* the insertion point overwrites that, the program's
/// reported type would flip from whatever the previous non-function
/// statement produced to `Undefined`. Function declarations don't
/// update the result, so e.g. `[x + 1;, function f() {}]` has type
/// `Number` in p but would become `Undefined` in q if we inserted a
/// `;` before the trailing function decl.
///
/// We sidestep that by only inserting at positions where some later
/// statement is still a result-setter (i.e. not Function or Empty).
/// That keeps the transformation sound for the stronger oracle that
/// compares program types, without having to weaken the oracle.
pub fn t_intersperse_empty(p: &Program) -> (Program, Comparison) {
    if p.statements.len() < 2 {
        return (p.clone(), Comparison::identity());
    }
    let is_result_setter = |s: &Stmt| !matches!(s, Stmt::FunctionDecl { .. } | Stmt::Empty { .. });

    let mut out = Vec::with_capacity(p.statements.len() * 2);
    for (i, stmt) in p.statements.iter().enumerate() {
        out.push(stmt.clone());
        if i + 1 < p.statements.len() {
            let later_has_setter = p.statements[i + 1..].iter().any(is_result_setter);
            if later_has_setter {
                out.push(empty_stmt());
            }
        }
    }
    (
        Program {
            statements: out,
            span: span(),
            type_aliases: Vec::new(),
            class_brands: Vec::new(),
            class_bases: Vec::new(),
            language: inty::ast::SourceLanguage::JavaScript,
        },
        Comparison::identity(),
    )
}

// -------------------------------------------------------------------------
// Swap adjacent independent statements.
// -------------------------------------------------------------------------

/// T: swap two adjacent statements that don't reference each other's
/// bindings. Restricted to:
///
/// - non-final pairs (the program's reported type is the last
///   statement's type, which we want to preserve), and
/// - pairs where *neither* statement is a `FunctionDecl`.
///
/// The function-decl exclusion sidesteps a known limitation in
/// inty's hoisting: only *adjacent* function declarations are
/// grouped into one binding scope for mutual-recursion purposes, so a
/// swap that breaks adjacency changes whether two functions can see
/// each other (see `tests/metamorphic.rs` commit history for the
/// failing case that motivated this restriction). Until inty
/// switches to a dependency-graph-based letrec grouping, swaps
/// involving function decls can genuinely change type-check outcomes
/// in a way that's not a metamorphic-property bug.
///
/// Returns `None` if no swappable pair exists, which lets the caller
/// `prop_assume!` the case away.
pub fn t_swap_first_independent_pair(p: &Program) -> Option<(Program, Comparison)> {
    let n = p.statements.len();
    if n < 3 {
        return None;
    }
    // Refuse pairs where every statement after them is a function
    // decl or empty: the program's reported type is the type of the
    // last non-function-decl statement, and swapping two distinct
    // setters with only function decls trailing would change which
    // one is "last" and therefore which type the program reports.
    let is_result_setter = |s: &Stmt| !matches!(s, Stmt::FunctionDecl { .. } | Stmt::Empty { .. });

    for i in 0..n - 2 {
        let a = &p.statements[i];
        let b = &p.statements[i + 1];

        // Sidestep inty's adjacency-sensitive function hoisting.
        if matches!(a, Stmt::FunctionDecl { .. }) || matches!(b, Stmt::FunctionDecl { .. }) {
            continue;
        }

        // The swap is only program-type-preserving if *some* setter
        // appears strictly after the swapped pair — otherwise one of
        // the swapped statements is itself the last setter and moving
        // it changes which type is reported.
        if !p.statements[i + 2..].iter().any(is_result_setter) {
            continue;
        }

        let bound_a = bound_names_in_stmt(a);
        let bound_b = bound_names_in_stmt(b);

        // Same-name binders can't be reordered — reordering changes
        // which initialiser wins.
        if !bound_a.is_disjoint(&bound_b) {
            continue;
        }

        let refs_a = referenced_names_in_stmt(a);
        let refs_b = referenced_names_in_stmt(b);

        if refs_a.is_disjoint(&bound_b) && refs_b.is_disjoint(&bound_a) {
            let mut statements = p.statements.clone();
            statements.swap(i, i + 1);
            return Some((
                Program {
                    statements,
                    span: span(),
                    type_aliases: Vec::new(),
                    class_brands: Vec::new(),
                    class_bases: Vec::new(),
                    language: inty::ast::SourceLanguage::JavaScript,
                },
                Comparison::identity(),
            ));
        }
    }
    None
}

// -------------------------------------------------------------------------
// Alpha-renaming: rename an existing top-level binding consistently
// throughout the whole program.
//
// The transformation picks a name that's actually bound in `p` and
// rewrites every occurrence (binder or reference) to a globally fresh
// name. Because the target name is fresh *everywhere* — not just in
// outer scope — the unconditional rename is alpha-equivalent, even in
// the presence of nested shadowing: an inner binder named `x` simply
// becomes a (still-shadowing) inner binder named `y`, and inner
// references continue to bind to it.
//
// The oracle compares the renamed binding's scheme in q against the
// original binding's scheme in p via an explicit rename pair.
// -------------------------------------------------------------------------

pub fn t_alpha_rename_existing(p: &Program) -> Option<(Program, Comparison)> {
    // Collect candidate renamable names — we only rename *top-level*
    // binders. That makes the comparison spec simple (one entry in
    // `rename`) without losing generality: inner binders still get
    // renamed by the unconditional substitution pass, but their names
    // aren't in the final program's top-level env so they don't show
    // up in the bindings map anyway.
    let candidates: Vec<String> = p
        .statements
        .iter()
        .flat_map(|s| bound_names_in_stmt(s).into_iter())
        .collect();
    let old = candidates.into_iter().next()?;

    let new = fresh_name("__metamorphic_renamed_", &names_in(p));
    let transformed = rename_all(p, &old, &new);
    Some((transformed, Comparison::identity().with_rename(old, new)))
}

// -------------------------------------------------------------------------
// Comma-wrap every bare expression statement: `e;` → `(0, e);`.
//
// JavaScript's comma operator evaluates its operands left-to-right and
// returns the last. Wrapping in `(0, e)` discards the 0 and yields `e`,
// so the statement's runtime effect and type both stay the same. The
// pretty-printer emits the parens via `needs_parens` only when the
// Sequence sits in a context that requires them; at the top of an
// expression statement `e, 0` would *not* get parens, which could
// confuse the parser if other statements sat on the same line. We side-
// step that by wrapping the Sequence in a Conditional-like form? No —
// just use `needs_parens=true` via nesting. Simpler: build a call to
// an IIFE that returns e. That's cleaner but has its own issues with
// `this`. The pragmatic choice: only wrap expression statements, and
// always re-parenthesise the Sequence by wrapping it in another comma
// with a single inner expression — then the outer emits parens.
//
// We pick the simplest form that round-trips: replace `e;` with
// `(function () { return e; })();`. The lambda captures nothing and
// has no this reference, so it's type-equivalent to `e` for everything
// the type checker cares about (primitives, objects, arrays, functions).
// This also avoids the Sequence-parens pretty-printer ambiguity.
//
// Caveat: a function boundary widens fresh literal returns (`return
// 1` becomes `Number`, not `Lit("1")`), so wrapping the expression
// statement that supplies the program-level type would change it.
// The program type is the type of the last statement that *isn't* a
// hoisted function-like decl (those are processed as a group and
// don't bump the running result), so we skip wrapping the last such
// expression statement — every other expression statement still
// exercises the wrap.
// -------------------------------------------------------------------------

fn is_hoisted_decl(s: &Stmt) -> bool {
    matches!(s, Stmt::FunctionDecl { .. } | Stmt::Empty { .. })
}

pub fn t_wrap_expr_statements(p: &Program) -> (Program, Comparison) {
    // Index of the last expression statement that contributes to the
    // program-level type (i.e., the last expression statement before
    // any trailing run of hoisted decls / empty statements).
    let mut skip_idx: Option<usize> = None;
    for (i, s) in p.statements.iter().enumerate() {
        if matches!(s, Stmt::Expr { .. }) {
            // Only this expression statement is "the last expression
            // statement that determines the program type" if every
            // statement after it is hoisted / empty.
            if p.statements[i + 1..].iter().all(is_hoisted_decl) {
                skip_idx = Some(i);
            }
        }
    }
    let statements: Vec<Stmt> = p
        .statements
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            Stmt::Expr { expression, span } if Some(i) != skip_idx => Stmt::Expr {
                expression: wrap_in_iife(expression.clone(), *span),
                span: *span,
            },
            other => other.clone(),
        })
        .collect();
    (
        Program {
            statements,
            span: span(),
            type_aliases: Vec::new(),
            class_brands: Vec::new(),
            class_bases: Vec::new(),
            language: inty::ast::SourceLanguage::JavaScript,
        },
        Comparison::identity(),
    )
}

fn wrap_in_iife(expr: Expr, s: Span) -> Expr {
    // (function () { return <expr>; })()
    let body = Stmt::Block {
        body: vec![Stmt::Return {
            argument: Some(expr),
            span: s,
        }],
        span: s,
    };
    let func = Expr::Function {
        name: None,
        params: vec![],
        body: Box::new(body),
        type_annotation: None,
        span: s,
    };
    Expr::Call {
        callee: Box::new(func),
        arguments: vec![],
        keywords: vec![],
        span: s,
    }
}

// -------------------------------------------------------------------------
// Destructuring equivalence: checked as a pair-of-programs test at the
// source level, because inty's parser desugars destructuring patterns
// into ordinary `VarDeclarator`s at parse time. That means we can't
// build a destructuring-shaped AST directly — we have to go via source
// text and let the parser produce the lowered form.
//
// The `build_destructure_pair` helper returns two source snippets that
// should type-check identically: one using explicit member access, one
// using the `{prop: x} = obj` destructuring sugar.
// -------------------------------------------------------------------------

// -------------------------------------------------------------------------
// Logical-assignment desugar equivalence.
//
// `a ??= b` differs from `a = a ?? b` only in short-circuit evaluation
// (RHS skipped when LHS test fails). The two forms must produce the
// same inferred types — that's the type-level invariant we're pinning.
// Same for `||=` / `||` and `&&=` / `&&`.
//
// We don't claim it as a per-expression rewrite inside `transform.rs`
// because the source-pair shape is simpler to reason about and the
// generator's `program_strategy()` doesn't emit logical-assignment ops
// itself (so a generic transform would have nothing to apply to).
// -------------------------------------------------------------------------

/// Build two equivalent source snippets:
///   `var x = <init>; x <op> <rhs>;`     (logical-assignment form)
///   `var x = <init>; x = x <bin> <rhs>;` (manually-desugared form)
///
/// `op` is one of `"??="`, `"||="`, `"&&="`; the corresponding
/// short-circuit binary op (`??`, `||`, `&&`) is selected automatically.
pub fn build_logical_assign_pair(op: &str, init: &str, rhs: &str) -> (String, String, Comparison) {
    let bin = match op {
        "??=" => "??",
        "||=" => "||",
        "&&=" => "&&",
        other => panic!("build_logical_assign_pair: unknown op `{other}`"),
    };
    let src_a = format!("var x = {init}; x {op} {rhs};");
    let src_b = format!("var x = {init}; x = x {bin} {rhs};");
    (src_a, src_b, Comparison::identity())
}

/// Build two equivalent source snippets. Returns the pair plus a
/// comparison that ignores the differently-named temp bindings each
/// side introduces.
pub fn build_destructure_pair(obj_src: &str, prop: &str) -> (String, String, Comparison) {
    let src_a = format!(
        "var __metamorphic_tmp = {obj}; var x = __metamorphic_tmp.{prop};",
        obj = obj_src,
        prop = prop,
    );
    // The parser synthesises `$destr$0` for the destructuring temp.
    // If this ever changes upstream, this test will break loudly; the
    // comparison spec names the temp explicitly rather than matching
    // by prefix to keep the test's expectation obvious.
    let src_b = format!("var {{{prop}: x}} = {obj};", prop = prop, obj = obj_src,);
    let cmp = Comparison::identity()
        .with_p_only(vec!["__metamorphic_tmp".to_string()])
        .with_q_only(vec!["$destr$0".to_string()]);
    (src_a, src_b, cmp)
}

// -------------------------------------------------------------------------
// Forward-reference reorder.
//
// Pre-hoisting top-level Var/Let/Const declarations (commit 472cccb)
// means a function body can reference a name that appears *later* in
// source order and still type-check, matching the JS/TS hoisting
// model. The metamorphic property is: moving a referenced
// `var`/`let`/`const` from before a function-decl that uses it to
// *after* that function-decl should not change the inferred types.
//
// Both directions of the swap should preserve check results. This
// transform exercises the "move down" direction (data decl appears
// earlier in `p` than in `q`), which is the harder direction —
// without hoisting, `q` would fail with "Undefined variable" inside
// the function body.
// -------------------------------------------------------------------------

/// Find the first `(var_idx, fn_idx)` pair where:
///   - `var_idx < fn_idx`
///   - statement at `var_idx` is a non-destructuring `var`/`let`/`const`
///     binding exactly one name (no shadowing complications)
///   - statement at `fn_idx` is a `function` declaration that
///     references the var-bound name
///   - no statement between them rebinds or references the name
///     in a way that would change with reordering
///
/// Returns `q` with the var decl moved to just after the function
/// decl, and an identity comparison.
pub fn t_move_data_decl_after_first_user(p: &Program) -> Option<(Program, Comparison)> {
    use inty::ast::{ExportDecl, Stmt, VarDeclarator};

    fn single_binding<'a>(s: &'a Stmt) -> Option<(&'a VarDeclarator, bool)> {
        // Returns (declarator, is_export). Only single-name, non-destructuring
        // forms qualify; multi-decl `var a = 1, b = 2;` is skipped because
        // the move would split it.
        match s {
            Stmt::Var { declarations, .. } if declarations.len() == 1 => {
                let d = &declarations[0];
                if d.name.starts_with("$destr$") {
                    return None;
                }
                Some((d, false))
            }
            Stmt::Export {
                declaration: ExportDecl::Var { declarations, .. },
                ..
            } if declarations.len() == 1 => {
                let d = &declarations[0];
                if d.name.starts_with("$destr$") {
                    return None;
                }
                Some((d, true))
            }
            _ => None,
        }
    }

    let n = p.statements.len();
    for var_idx in 0..n.saturating_sub(1) {
        let Some((decl, _is_export)) = single_binding(&p.statements[var_idx]) else {
            continue;
        };
        let name = decl.name.clone();

        // Find the first function decl after var_idx that *references*
        // this name in its body. Function-decl-form only (not function
        // expressions assigned to a var) because the SCC pass treats
        // function decls specially.
        for fn_idx in (var_idx + 1)..n {
            let fn_stmt = &p.statements[fn_idx];
            let is_fn_decl = matches!(fn_stmt, Stmt::FunctionDecl { .. })
                || matches!(
                    fn_stmt,
                    Stmt::Export {
                        declaration: ExportDecl::Function { .. },
                        ..
                    }
                );
            if !is_fn_decl {
                continue;
            }
            let refs = referenced_names_in_stmt(fn_stmt);
            if !refs.contains(&name) {
                continue;
            }

            // Check no intermediate statement rebinds or references
            // the name. Rebinding would change which initialiser the
            // function sees after the move; an intermediate reference
            // would observe the un-initialised hoisted variable post-
            // move, which is a real TDZ-style difference.
            let between_ok = p.statements[var_idx + 1..fn_idx]
                .iter()
                .chain(p.statements[fn_idx + 1..].iter().take(1))
                .all(|s| {
                    !bound_names_in_stmt(s).contains(&name)
                        && !referenced_names_in_stmt(s).contains(&name)
                });
            if !between_ok {
                continue;
            }
            // Also: nothing after the function uses the name before
            // the function would have completed type-checking it.
            // Conservatively skip if any non-function-decl statement
            // between var and fn references the name.
            let no_uses_before_fn = p.statements[var_idx + 1..fn_idx]
                .iter()
                .all(|s| !referenced_names_in_stmt(s).contains(&name));
            if !no_uses_before_fn {
                continue;
            }

            // Build q by moving the var decl from `var_idx` to just
            // after `fn_idx`.
            let mut statements = p.statements.clone();
            let var_stmt = statements.remove(var_idx);
            // After removal, the function-decl that was at fn_idx is
            // now at fn_idx - 1. Insert the var decl just after it.
            statements.insert(fn_idx, var_stmt);
            return Some((
                Program {
                    statements,
                    span: span(),
                    type_aliases: Vec::new(),
                    class_brands: Vec::new(),
                    class_bases: Vec::new(),
                    language: inty::ast::SourceLanguage::JavaScript,
                },
                Comparison::identity(),
            ));
        }
    }
    None
}
