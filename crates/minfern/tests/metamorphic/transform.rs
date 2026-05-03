//! Semantics-preserving transformations on `Program` ASTs. Each returns
//! the transformed program together with a [`Comparison`] that describes
//! how the transformation renamed / introduced / removed bindings, so
//! the oracle can assert the appropriate equivalence.

use minfern::lexer::Span;
use minfern::parser::ast::*;

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
    let is_result_setter =
        |s: &Stmt| !matches!(s, Stmt::FunctionDecl { .. } | Stmt::Empty { .. });

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
/// minfern's hoisting: only *adjacent* function declarations are
/// grouped into one binding scope for mutual-recursion purposes, so a
/// swap that breaks adjacency changes whether two functions can see
/// each other (see `tests/metamorphic.rs` commit history for the
/// failing case that motivated this restriction). Until minfern
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
    let is_result_setter =
        |s: &Stmt| !matches!(s, Stmt::FunctionDecl { .. } | Stmt::Empty { .. });

    for i in 0..n - 2 {
        let a = &p.statements[i];
        let b = &p.statements[i + 1];

        // Sidestep minfern's adjacency-sensitive function hoisting.
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
    Some((
        transformed,
        Comparison::identity().with_rename(old, new),
    ))
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
// -------------------------------------------------------------------------

pub fn t_wrap_expr_statements(p: &Program) -> (Program, Comparison) {
    let statements: Vec<Stmt> = p
        .statements
        .iter()
        .map(|s| match s {
            Stmt::Expr { expression, span } => Stmt::Expr {
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
        span: s,
    }
}

// -------------------------------------------------------------------------
// Destructuring equivalence: checked as a pair-of-programs test at the
// source level, because minfern's parser desugars destructuring patterns
// into ordinary `VarDeclarator`s at parse time. That means we can't
// build a destructuring-shaped AST directly — we have to go via source
// text and let the parser produce the lowered form.
//
// The `build_destructure_pair` helper returns two source snippets that
// should type-check identically: one using explicit member access, one
// using the `{prop: x} = obj` destructuring sugar.
// -------------------------------------------------------------------------

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
    let src_b = format!(
        "var {{{prop}: x}} = {obj};",
        prop = prop,
        obj = obj_src,
    );
    let cmp = Comparison::identity()
        .with_p_only(vec!["__metamorphic_tmp".to_string()])
        .with_q_only(vec!["$destr$0".to_string()]);
    (src_a, src_b, cmp)
}
