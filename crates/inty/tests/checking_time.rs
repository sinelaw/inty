//! Checking time stays proportional to a program's size where annotations
//! name record types with many function fields (Rosaclef's `Ctx`, with
//! about 25 canvas methods, `Ev`, `Builder`).
//!
//! Since 74c2460 every such field was a method whose `this` was the
//! record itself, so each annotation built and unified fresh recursive
//! rows: Rosaclef's `tree/memory.js` went from 15 ms to 5 s and the whole
//! frontend ran out of memory. A function type in an object type now uses
//! no `this` (a method signature, `m(): T`, says otherwise), and the
//! program below checks in a fifth of a second in a release build (10 s
//! at cb4bfca).

use std::time::{Duration, Instant};

/// A program whose functions take the three record types, each call
/// reading their function fields.
fn program(n_methods: usize, n_funcs: usize) -> String {
    let ctx: Vec<String> = (0..n_methods)
        .map(|i| format!("m{i}: (Number, Number) => Undefined"))
        .collect();
    let mut src = vec![
        format!("/** type Ctx = {{ {}, width: Number }} */", ctx.join(", ")),
        "/** type Ev = { preventDefault: () => Undefined, stopPropagation: () => Undefined, \
         x: Number } */"
            .to_string(),
        "/** type Builder = { add: (String) => Undefined, done: () => String, ctx: Ctx } */"
            .to_string(),
    ];
    for k in 0..n_funcs {
        let body: Vec<String> = (0..6)
            .map(|i| format!("c.m{}(e.x, {i});", (k + i) % n_methods))
            .collect();
        src.push(format!(
            "/** function f{k}(c: Ctx, e: Ev, b: Builder) => Number */"
        ));
        src.push(format!(
            "function f{k}(c, e, b) {{ e.preventDefault(); {} b.add(\"x\"); \
             b.ctx.m0(1, 2); return c.width + {k}; }}",
            body.join(" ")
        ));
    }
    let methods: Vec<String> = (0..n_methods)
        .map(|i| format!("m{i}: (a, b) => undefined"))
        .collect();
    src.push("/** function make() => Builder */".to_string());
    src.push(format!(
        "function make() {{ /** const parts: String[] */ const parts = []; \
         /** const c: Ctx */ const c = {{ {}, width: 1 }}; \
         return {{ add: (s) => {{ parts.push(s); }}, done: () => parts.join(\"\"), ctx: c }}; }}",
        methods.join(", ")
    ));
    src.join("\n")
}

#[test]
fn records_of_functions_check_quickly() {
    let src = program(25, 60);
    let program = inty::frontends::javascript::parse_source(&src).expect("parses");
    let start = Instant::now();
    let errors = inty::worker::run_with_inference_stack("inty-checking-time", move || {
        let (env, mut state) = inty::stdlib::initial_env_with_stdlib().expect("stdlib");
        let result = state.infer_program_with_env(&env, &program).map(|_| ());
        let mut errors: Vec<String> = state.take_errors().iter().map(|e| e.to_string()).collect();
        if let Err(e) = result.and_then(|()| state.resolve_constraints()) {
            errors.push(e.to_string());
        }
        errors
    });
    let elapsed = start.elapsed();
    assert!(errors.is_empty(), "{errors:?}");
    // A debug build takes about a second (and checking time grows with the
    // number of functions); cb4bfca's grew faster, to about half a minute.
    assert!(
        elapsed < Duration::from_secs(10),
        "checking took {elapsed:?}: records of functions are expensive again"
    );
}
