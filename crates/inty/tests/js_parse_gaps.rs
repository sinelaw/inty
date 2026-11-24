//! JavaScript the parser and stdlib take: `export class`, the
//! contextual keywords `from` / `of` / `as` as names, array-pattern
//! holes, default and destructuring parameters on class methods and
//! constructors, constructor statements other than `this.f = …`, and the
//! builtins `new Promise(executor)`, `EventSource`, the full
//! `XMLHttpRequest.open` and a regex's writable `lastIndex`.

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

fn ok(src: &str) {
    let r = check(src);
    assert!(r.is_ok(), "should check: {:?}\n{}", r, src);
}

fn fails(src: &str, needle: &str) {
    let r = check(src);
    match r {
        Err(e) => assert!(e.contains(needle), "expected {:?} in {}", needle, e),
        Ok(()) => panic!("should not check:\n{}", src),
    }
}

#[test]
fn export_class() {
    ok(
        "export class A { constructor(n) { this.n = n; } twice() { return this.n * 2; } }\n\
        const x = new A(3).twice() + 1;\n",
    );
}

#[test]
fn contextual_keywords_are_names() {
    ok(
        "const from = 1;\nconst as = from + 1;\nconst of = [from, as];\n\
        for (const x of of) { const y = x + 1; }\n",
    );
}

#[test]
fn array_pattern_holes() {
    ok(
        "const t = [1, 2, 3];\nconst [a, , c] = t;\nconst [, b] = t;\n\
        let u = 0, v = 0;\n[u, , v] = t;\nconst s = a + b + c + u + v;\n",
    );
}

#[test]
fn method_default_and_destructuring_parameters() {
    ok(
        "class A { m(x, opts = {k: 1}) { return x + opts.k; } n({a, b}) { return a + b; } }\n\
        const r = new A().m(1, {k: 2}) + new A().n({a: 1, b: 2});\n",
    );
}

#[test]
fn whole_parameter_pattern_default() {
    ok("function f(x, {scale} = {scale: 1}) { return x * scale; }\nconst r = f(1, {scale: 2});\n");
}

#[test]
fn constructor_statements_run_between_fields() {
    ok("class A {\n\
          constructor(n) {\n\
            const m = n + 1;\n\
            this.n = m;\n\
            let k = this.n * 2;\n\
            if (k > 10) k = 10;\n\
            for (const x of [1, 2]) k += x;\n\
            this.k = k;\n\
          }\n\
        }\n\
        const t = new A(1).k + 1;\n");
}

#[test]
fn constructor_keeps_its_limits() {
    fails(
        "class B { constructor(n) { if (n) { this.x = n; } } }",
        "storing to a field of `this` inside an expression",
    );
    fails(
        "class C { constructor(n) { return; } }",
        "`return` in the constructor",
    );
    fails(
        "class D { constructor(n) { const q = 1; this.q = q; } read() { return q; } }",
        "which the constructor also declares",
    );
}

#[test]
fn promise_constructor() {
    ok("const p = new Promise((resolve) => resolve(1));\nconst q = p.then((n) => n + 1);\n\
        const r = new Promise((resolve, reject) => { if (Math.random() > 0.5) resolve(\"a\"); else reject(\"e\"); });\n");
}

#[test]
fn event_source_and_xhr_open() {
    ok("const es = new EventSource(\"/events\");\n\
        es.onmessage = (e) => { const n = e.data.length; };\n\
        es.addEventListener(\"ping\", (e) => e.lastEventId.length);\nes.close();\n\
        const x = new XMLHttpRequest();\nx.open(\"POST\", \"/api\", false);\n");
}

#[test]
fn regex_last_index_is_writable() {
    ok("const re = /b/g;\nre.lastIndex = 0;\nconst n = re.lastIndex + 1;\n");
    fails("const re = /b/g;\nre.lastIndex = \"x\";\n", "Number");
    fails("const re = /b/g;\nre.source = \"y\";\n", "FieldWrite");
}

#[test]
fn async_methods_keep_this() {
    ok("class A {\n\
          constructor(n) { this.n = n; }\n\
          async load(x) { const y = await Promise.resolve(x); return y + this.n; }\n\
        }\n\
        const q = new A(1).load(2).then((v) => v * 2);\n\
        const o = { k: 1, async f(x) { return x + this.k; } };\n\
        const r = o.f(1).then((v) => v + 1);\n");
    fails(
        "class A { async constructor() {} }",
        "a getter, setter or constructor can't be async",
    );
}

#[test]
fn keyword_and_async_named_members() {
    ok("class A { delete(k) { return k + 1; } default() { return \"d\"; } async() { return 1; } }\n\
        const a = new A();\nconst n = a.delete(1) + a.async() + a.default().length;\n\
        const o = { delete(k) { return k; }, async: 1 };\nconst m = o.delete(1) + o.async;\n");
}
