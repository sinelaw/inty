//! Regression tests for the bugs found while type-checking Rosaclef, a
//! ~6k-line vanilla-JS DAW frontend built on inty (see
//! `docs/patterns.md`). Each test is the minimal repro from the bug
//! report; the numbers refer to that report.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

/// Type-check `src` against the stdlib; `Err` carries every diagnostic.
fn check(src: &str) -> Result<(), String> {
    let program = parse(src).map_err(|e| format!("parse error: {}", e))?;
    let (env, mut state) = initial_env_with_stdlib().map_err(|e| format!("stdlib: {}", e))?;
    let result = state.infer_program_with_env(&env, &program);
    let errors = state.take_errors();
    if !errors.is_empty() {
        let msgs: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
        return Err(msgs.join("\n"));
    }
    result.map_err(|e| e.to_string())?;
    state.resolve_constraints().map_err(|e| e.to_string())
}

#[track_caller]
fn ok(src: &str) {
    if let Err(e) = check(src) {
        panic!("expected to type-check, got:\n{}\n--- source ---\n{}", e, src);
    }
}

#[track_caller]
fn err(src: &str) -> String {
    match check(src) {
        Ok(()) => panic!("expected a type error\n--- source ---\n{}", src),
        Err(e) => e,
    }
}

// `new Date()` with no argument: the stdlib declared a required
// milliseconds argument, so every module using it failed.
#[test]
fn new_date_without_argument() {
    ok("const at = new Date().toISOString();");
    ok("const d = new Date(0); const t = d.getTime();");
}

// 1. A comparison of property reads on a module-level binding, inside a
// function declaration: `Number >= Int`.
#[test]
fn b1_compare_outer_property_reads() {
    ok("
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        function fix() { if (state.insert >= state.xs.length) state.insert = 0; }
        fix();
    ");
    ok("
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        function fix() { if (state.insert === state.xs.length) state.insert = 0; }
        fix();
    ");
    ok("
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        function f() { return state.insert + state.xs.length; }
        function g() { return state.insert < state.xs.length && state.xs.length <= state.insert; }
    ");
}

// 1. The function reads a binding declared after it.
#[test]
fn b1_function_before_declaration() {
    ok("
        function fix() { if (state.insert >= state.xs.length) state.insert = 0; }
        const state = { insert /*: Number */: 1, xs /*: Number[] */: [] };
        fix();
    ");
}

// 2. Narrowing a local whose type comes from a module-level binding.
#[test]
fn b2_narrowing_outer_find() {
    ok(r#"
        /** const XS: { name: String, v: String }[] */
        const XS = [{ name: "a", v: "x" }];
        /** function g(n: String) => String */
        function g(n) { const found = XS.find((i) => i.name === n); return found ? found.v : ""; }
    "#);
    ok(r#"
        /** const XS: String[][] */
        const XS = [["a", "x"]];
        /** function g(n: String) => String */
        function g(n) { const found = XS.find((i) => i[0] === n); return found !== undefined ? found[1] : ""; }
    "#);
}

#[test]
fn b2_narrowing_forms_on_outer_bindings() {
    let decls = r#"
        /** const XS: { name: String, v: String }[] */
        const XS = [{ name: "a", v: "x" }];
    "#;
    for body in [
        r#"const f = XS.find((i) => i.name === n); if (f === undefined) return ""; return f.v;"#,
        r#"const f = XS.find((i) => i.name === n); if (!f) return ""; return f.v;"#,
        r#"const f = XS.find((i) => i.name === n); if (f != null) return f.v; return "";"#,
        r#"const f = XS.find((i) => i.name === n); return f !== undefined ? f.v : "";"#,
    ] {
        ok(&format!(
            "{decls}\n/** function g(n: String) => String */\nfunction g(n) {{ {body} }}"
        ));
    }
}
