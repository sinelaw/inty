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

/// Like [`check`], with `lib` loaded first as a `--lib` declaration file.
fn check_with_lib(lib: &str, src: &str) -> Result<(), String> {
    let (env, mut state) = initial_env_with_stdlib().map_err(|e| format!("stdlib: {}", e))?;
    let env = inty::stdlib::load_lib(&mut state, env, lib).map_err(|e| format!("lib: {}", e))?;
    let program = parse(src).map_err(|e| format!("parse error: {}", e))?;
    let result = state.infer_program_with_env(&env, &program);
    let errors = state.take_errors();
    if !errors.is_empty() {
        let msgs: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
        return Err(msgs.join("\n"));
    }
    result.map_err(|e| e.to_string())?;
    state.resolve_constraints().map_err(|e| e.to_string())
}

// 3. An alias may refer to one declared after it.
#[test]
fn b3_alias_forward_reference() {
    ok("
        /** type R = { a: Number, xs: R2[] } */
        /** type R2 = { b: Number } */
        /** function f() => R */
        function f() { return { a: 1, xs: [{ b: 0 }] }; }
    ");
    ok("
        /** type Pair<T> = { l: Side<T>, r: Side<T> } */
        /** type Side<T> = { v: T } */
        /** const p: Pair<String> */
        const p = { l: { v: \"a\" }, r: { v: \"b\" } };
    ");
    err("
        /** type R = { xs: R2[] } */
        /** type R2 = { b: Number } */
        /** const r: R */
        const r = { xs: [{ b: \"no\" }] };
    ");
}

// 3. Recursive aliases are equi-recursive types; one that is defined as
// itself is an error that says so.
#[test]
fn b3_recursive_aliases() {
    ok("
        /** type Tree = { label: String, kids: Tree[] } */
        /** function size(t: Tree) => Int */
        function size(t) { let n = 1; for (const k of t.kids) n = n + size(k); return n; }
        const s = size({ label: \"a\", kids: [{ label: \"b\", kids: [] }] });
    ");
    ok("
        /** type A = { b: B | Null } */
        /** type B = { a: A } */
        /** const x: A */
        const x = { b: null };
        /** const y: A */
        const y = { b: { a: { b: null } } };
    ");
    ok("
        /** type List<T> = { head: T, tail: List<T> | Null } */
        /** const l: List<Int> */
        const l = { head: 1, tail: { head: 2, tail: null } };
    ");
    err("
        /** type Tree = { label: String, kids: Tree[] } */
        /** const t: Tree */
        const t = { label: \"a\", kids: [{ label: 1, kids: [] }] };
    ");
    let e = err("/** type Bad = Bad */ const x = 1;");
    assert!(e.contains("'Bad' is defined as itself"), "{e}");
}

// 4. A class in a --lib file is a type for the aliases of the same file.
#[test]
fn b4_lib_class_visible_to_aliases() {
    let lib = "
        class InsertIx {}
        /** type Channel = { name: String, mixer: InsertIx } */
    ";
    check_with_lib(
        lib,
        "/** const c: Channel */ const c = { name: \"a\", mixer: new InsertIx() };",
    )
    .unwrap();
    // Still nominal: a different class is rejected.
    let e = check_with_lib(
        &format!("{lib}\nclass TrackIx {{}}"),
        "/** const c: Channel */ const c = { name: \"a\", mixer: new TrackIx() };",
    );
    assert!(e.is_err());
    // In an ordinary module too, whichever comes first.
    ok("
        /** type Channel = { mixer: InsertIx } */
        class InsertIx {}
        /** const c: Channel */
        const c = { mixer: new InsertIx() };
    ");
}

// 5. A non-literal `Int` flows into a `Number` field of a returned
// record: the annotation is pushed into the function literal.
#[test]
fn b5_int_into_number_positions() {
    ok("
        /** type S = { elements: Number } */
        /** const f: () => S */
        const f = () => ({ elements: [1, 2].length });
    ");
    ok("
        /** type S = { elements: Number, xs: Number[] } */
        /** function f(x: Number) => S */
        function f(x) { return { elements: Math.round(x), xs: [Math.round(x), 0.5] }; }
    ");
    ok("
        /** const p: Promise<{ n: Number }> */
        const p = Promise.resolve({ n: 1 });
        /** const g: (Int) => { n: Number } */
        const g = (i) => ({ n: i });
    ");
    // The fresh object's slot is a Number: it may later hold a fraction.
    ok("
        /** type S = { n: Number } */
        /** const f: () => S */
        const f = () => ({ n: [1].length });
        const s = f();
        s.n = 0.5;
    ");
    // An existing Int record is not a Number record (it could be written
    // a fraction through the other view).
    err("
        const r = { n: [1].length };
        /** const s: { n: Number } */
        const s = r;
    ");
}

// 5. A mutable field initialised with an integer literal holds fractions.
#[test]
fn b5_literal_initialised_field() {
    ok("const s = { volume: 1 }; s.volume = 0.5;");
    ok("const state = { volume: 1 }; function set() { state.volume = 0.25; } set();");
}

// 6. A callback may take fewer parameters than it is passed.
#[test]
fn b6_fewer_callback_parameters() {
    ok("const ys = [1, 2].map(() => \"a\");");
    ok("
        /** function each(f: (Int, String) => Undefined) => Undefined */
        function each(f) { f(1, \"a\"); return undefined; }
        each(() => undefined);
        each((i) => undefined);
    ");
    // Not more than it is passed.
    err("
        /** function each(f: (Int) => Undefined) => Undefined */
        function each(f) { f(1); return undefined; }
        each((i, j) => undefined);
    ");
}
