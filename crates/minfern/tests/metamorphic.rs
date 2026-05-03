//! Metamorphic property tests for the type checker.
//!
//! When there's no absolute oracle for "is this program well-typed?",
//! we can still assert a *relational* property: for some transformation
//! `T` that should preserve type-checker behaviour, `check(p) ≈ check(T(p))`.
//!
//! This file ties together four sub-modules (under `tests/metamorphic/`):
//!
//! - `ast`       — AST construction helpers, name collection,
//!                 capture-avoiding rename
//! - `strategy`  — proptest strategies that generate programs
//! - `oracle`    — `CheckResult`, `check`, and the consistency
//!                 assertion with rename/exclusion support
//! - `transform` — the actual transformations
//!
//! Each property test picks one transformation and asserts the
//! appropriate `Comparison` holds between `p` and `T(p)`.

#[path = "metamorphic/ast.rs"]
mod ast;
#[path = "metamorphic/oracle.rs"]
mod oracle;
#[path = "metamorphic/strategy.rs"]
mod strategy;
#[path = "metamorphic/transform.rs"]
mod transform;

use proptest::prelude::*;

use minfern::parser::{ast::Program, parse, pretty::print_program};

#[cfg(test)]
use oracle::CheckResult;
use oracle::{assert_consistent, check};
use strategy::program_strategy;
use transform::{
    build_destructure_pair, t_alpha_rename_existing, t_intersperse_empty, t_prepend_dead_var,
    t_prepend_empty, t_swap_first_independent_pair, t_wrap_expr_statements,
};

// Round-trip sanity: every generated program must pretty-print and
// re-parse. If this ever fails, every other property below stops
// meaning anything.
fn round_trips(p: &Program) -> bool {
    parse(&print_program(p)).is_ok()
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        max_shrink_iters: 1024,
        ..ProptestConfig::default()
    })]

    #[test]
    fn prop_strategy_round_trips(p in program_strategy()) {
        prop_assert!(round_trips(&p), "generator emitted a program that fails to round-trip:\n{}", print_program(&p));
    }

    #[test]
    fn prop_prepend_empty(p in program_strategy()) {
        prop_assume!(round_trips(&p));
        let (q, cmp) = t_prepend_empty(&p);
        prop_assume!(round_trips(&q));
        assert_consistent("prepend_empty", &p, &q, &cmp);
    }

    #[test]
    fn prop_prepend_dead_var(p in program_strategy()) {
        prop_assume!(round_trips(&p));
        let (q, cmp) = t_prepend_dead_var(&p);
        prop_assume!(round_trips(&q));
        assert_consistent("prepend_dead_var", &p, &q, &cmp);
    }

    #[test]
    fn prop_intersperse_empty(p in program_strategy()) {
        prop_assume!(round_trips(&p));
        let (q, cmp) = t_intersperse_empty(&p);
        prop_assume!(round_trips(&q));
        assert_consistent("intersperse_empty", &p, &q, &cmp);
    }

    #[test]
    fn prop_swap_independent(p in program_strategy()) {
        prop_assume!(round_trips(&p));
        let (q, cmp) = match t_swap_first_independent_pair(&p) {
            Some(pair) => pair,
            None => return Ok(()),
        };
        prop_assume!(round_trips(&q));
        assert_consistent("swap_independent", &p, &q, &cmp);
    }

    #[test]
    fn prop_alpha_rename(p in program_strategy()) {
        prop_assume!(round_trips(&p));
        let (q, cmp) = match t_alpha_rename_existing(&p) {
            Some(pair) => pair,
            None => return Ok(()),
        };
        prop_assume!(round_trips(&q));
        assert_consistent("alpha_rename", &p, &q, &cmp);
    }

    #[test]
    fn prop_wrap_expr_statements(p in program_strategy()) {
        prop_assume!(round_trips(&p));
        let (q, cmp) = t_wrap_expr_statements(&p);
        prop_assume!(round_trips(&q));
        assert_consistent("wrap_expr_statements", &p, &q, &cmp);
    }
}

// -------------------------------------------------------------------------
// Destructuring equivalence.
//
// Kept as a standalone proptest because the destructuring form has no
// direct AST representation — it's parsed and desugared into ordinary
// VarDeclarators. We build both source snippets, parse them, and assert
// the inferred shape for `x` agrees on both sides.
// -------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        max_shrink_iters: 512,
        ..ProptestConfig::default()
    })]

    #[test]
    fn prop_destructure_equivalent(
        obj_src in proptest::sample::select(vec![
            "{k: 1}".to_string(),
            "{k: \"hi\"}".to_string(),
            "{k: true}".to_string(),
            "{k: {inner: 1}}".to_string(),
            "{k: [1, 2, 3]}".to_string(),
            "{other: 1, k: 42}".to_string(),
        ]),
        prop in proptest::sample::select(vec!["k".to_string()]),
    ) {
        let (src_a, src_b, cmp) = build_destructure_pair(&obj_src, &prop);
        let p_a = parse(&src_a).unwrap_or_else(|e| panic!("src_a failed to parse: {:?}\nsrc: {}", e, src_a));
        let p_b = parse(&src_b).unwrap_or_else(|e| panic!("src_b failed to parse: {:?}\nsrc: {}", e, src_b));
        assert_consistent("destructure_equivalent", &p_a, &p_b, &cmp);
    }
}

// -------------------------------------------------------------------------
// Hand-written sanity tests. These guard the transformations themselves
// against silly bugs so random failures get attributed to the checker
// rather than the test harness.
// -------------------------------------------------------------------------

#[cfg(test)]
mod unit {
    use super::*;
    use super::ast::{bound_names_in_stmt, names_in, rename_all};
    use minfern::parser::ast::Stmt;

    fn p_from(src: &str) -> Program {
        parse(src).expect("source must parse")
    }

    #[test]
    fn check_ok_captures_bindings() {
        let p = p_from("var a = 1; var b = \"hi\";");
        match check(&p) {
            CheckResult::Ok(ok) => {
                assert!(ok.bindings.contains_key("a"));
                assert!(ok.bindings.contains_key("b"));
                assert!(!ok.bindings.contains_key("Math"), "stdlib names should be filtered out");
            }
            CheckResult::Err => panic!("expected ok"),
        }
    }

    #[test]
    fn prepend_empty_noop() {
        let p = p_from("var a = 1;");
        let (q, cmp) = t_prepend_empty(&p);
        assert_consistent("prepend_empty (concrete)", &p, &q, &cmp);
    }

    #[test]
    fn prepend_dead_var_excludes_injected_name() {
        let p = p_from("var a = 1; var b = a + 2;");
        let (q, cmp) = t_prepend_dead_var(&p);
        assert!(
            !cmp.q_only.is_empty(),
            "injected dead var must be listed as q_only"
        );
        assert_consistent("prepend_dead_var (concrete)", &p, &q, &cmp);
    }

    #[test]
    fn alpha_rename_preserves_type_under_rename() {
        let p = p_from("var a = 1; var b = a + 2;");
        let (q, cmp) = t_alpha_rename_existing(&p).expect("program has bindings to rename");
        let (old, new) = cmp.rename.first().expect("rename has one entry");
        // Rename should pick up `a` or `b` on the p side.
        assert!(old == "a" || old == "b");
        // New name should actually be in q's AST.
        assert!(names_in(&q).contains(new));
        assert_consistent("alpha_rename (concrete)", &p, &q, &cmp);
    }

    #[test]
    fn alpha_rename_propagates_into_nested_scopes() {
        // Renaming outer `x` should also rename the inner shadowing `x`.
        // Unconditional rename is safe here because the target is
        // globally fresh.
        let p = p_from("var x = 1; function f() { var x = 2; return x; }");
        let q = rename_all(&p, "x", "__metamorphic_renamed_x_0");
        let q_names = names_in(&q);
        assert!(q_names.contains("__metamorphic_renamed_x_0"));
        assert!(!q_names.contains("x"));
    }

    #[test]
    fn swap_finds_non_final_pair() {
        // Need >= 3 statements because the last is off-limits.
        let p = p_from("var a = 1; var b = 2; var c = 0;");
        let (q, _) = t_swap_first_independent_pair(&p)
            .expect("(a, b) is an independent non-final pair");
        if let Stmt::Var { declarations, .. } = &q.statements[0] {
            assert_eq!(declarations[0].name, "b");
        } else {
            panic!("expected a var decl as first statement of q");
        }
    }

    #[test]
    fn swap_refuses_dependent_pair() {
        let p = p_from("var a = 1; var b = a; var c = 0;");
        assert!(t_swap_first_independent_pair(&p).is_none());
    }

    #[test]
    fn wrap_expr_statement_keeps_program_type() {
        let p = p_from("var x = 1; x + 1;");
        let (q, cmp) = t_wrap_expr_statements(&p);
        assert_consistent("wrap_expr_statements (concrete)", &p, &q, &cmp);
    }

    #[test]
    fn destructure_concrete() {
        let (src_a, src_b, cmp) = build_destructure_pair("{k: 42}", "k");
        let p_a = parse(&src_a).unwrap();
        let p_b = parse(&src_b).unwrap();
        assert_consistent("destructure_equivalent (concrete)", &p_a, &p_b, &cmp);
    }

    #[test]
    fn bound_names_function_decl() {
        let s = match &p_from("function f(a, b) { return a; }").statements[0] {
            Stmt::FunctionDecl { .. } => p_from("function f(a, b) { return a; }")
                .statements[0]
                .clone(),
            _ => unreachable!(),
        };
        let bound = bound_names_in_stmt(&s);
        // Only the function's own name is bound at its statement site
        // (params belong to the inner scope).
        assert!(bound.contains("f"));
        assert!(!bound.contains("a"));
    }
}
