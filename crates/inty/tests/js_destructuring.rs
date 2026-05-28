//! End-to-end tests for JavaScript destructuring *assignment*
//! (`[a, b] = e`, `({a} = e)`) — assigning to already-declared targets,
//! as opposed to destructuring *declarations* (`let [a, b] = e`).

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src`; return Ok(()) if it checks, or the formatted error.
fn check(src: &str) -> Result<(), String> {
    let program = parse(src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    let errs = state.take_errors();
    if errs.is_empty() {
        Ok(())
    } else {
        Err(format!("{:?}", errs))
    }
}

#[test]
fn array_destructuring_assignment() {
    let r = check("let x = 0, y = 0;\n[x, y] = [1, 2];\nlet z = x + y;\n");
    assert!(
        r.is_ok(),
        "array destructuring assignment should check: {:?}",
        r
    );
}

#[test]
fn object_destructuring_assignment_parenthesised() {
    let r = check("let a = 0;\n({a} = {a: 5});\nlet b = a + 1;\n");
    assert!(
        r.is_ok(),
        "object destructuring assignment should check: {:?}",
        r
    );
}

#[test]
fn array_destructuring_with_rest() {
    let r = check("let h = 0, t = [0];\n[h, ...t] = [1, 2, 3];\nlet z = h + t[0];\n");
    assert!(
        r.is_ok(),
        "rest destructuring assignment should check: {:?}",
        r
    );
}

#[test]
fn destructuring_assignment_enforces_types() {
    // `[n, s] = [1, 2]` makes `s` a Number (the array is Number[]); using
    // it as a String is then a type error.
    let r = check("let n = 0;\nlet s = \"\";\n[n, s] = [1, 2];\ns.toUpperCase();\n");
    assert!(
        r.is_err(),
        "type mismatch through destructuring should be caught"
    );
}

#[test]
fn nested_destructuring_assignment() {
    let r = check("let a = 0, b = 0;\nlet o = {p: [0, 0]};\n({p: [a, b]} = o);\nlet z = a + b;\n");
    assert!(
        r.is_ok(),
        "nested destructuring assignment should check: {:?}",
        r
    );
}

#[test]
fn invalid_assignment_target_still_rejected() {
    // A non-destructuring invalid target (e.g. a call) must still error.
    let r = check("let f = function() { return 1; };\nf() = 1;\n");
    assert!(
        r.is_err(),
        "assigning to a call result must still be rejected"
    );
}
