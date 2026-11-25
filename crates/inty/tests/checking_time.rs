//! Checking time stays proportional to a program's size where annotations
//! name record types with many function fields (Rosaclef's `Ctx`, with
//! about 25 canvas methods, `Ev`, `Builder`).
//!
//! Since 74c2460 every such field was a method whose `this` was the
//! record itself, so each annotation built and unified fresh recursive
//! rows: Rosaclef's `tree/memory.js` went from 15 ms to 5 s and the whole
//! frontend ran out of memory. A function type in an object type now uses
//! no `this` (a method says its `this`: `m: (this: T) => R`), and the
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

/// A class method building nested elements with `appendChild`, the
/// result handed to a field of unknown type: the field's `appendChild`
/// waits as a constraint whose argument is the element tree, and
/// generalising the class wrote that constraint out in full — elements
/// mention each other in cycles, so it came to about 16 million nodes
/// (20 s, and out of memory on a real client). Such a constraint now
/// counts towards "too large to generalise", as the type does.
#[test]
fn nested_elements_in_a_class_check_quickly() {
    check_quickly(&nested_elements_class());
}

/// A method of an object literal testing a field that holds an element
/// tree (`if (this.el)`): the test asks only whether the value may be a
/// function or a promise, which its head says. Resolving the whole type to
/// ask wrote the tree out (out of memory on a real client, once fields
/// were typed before methods made `this.el` known at the test).
#[test]
fn testing_an_element_field_checks_quickly() {
    let mut src = vec!["export function mk(parent) {".to_string()];
    src.push("  const root = document.createElement('div');".to_string());
    let mut prev = "root".to_string();
    for i in 1..5 {
        src.push(format!(
            "  const d{i} = document.createElement('span'); d{i}.textContent = 'x'; \
             {prev}.appendChild(d{i});"
        ));
        prev = format!("d{i}");
    }
    src.push("  parent.appendChild(root);".to_string());
    src.push(
        "  const o = { el: root, parent, m() { if (this.el) { return 1; } \
         if (this.parent) { return 2; } return 0; } };\n  return o;\n}"
            .to_string(),
    );
    check_quickly(&src.join("\n"));
}

/// A test narrowing a binding that holds an element (`const p =
/// this.el.parentElement; if (p !== null)`, `const el = this.el; if
/// (el)`): narrowing looks at the binding's head and a union's members,
/// and resolving its whole type to do so wrote the element tree out (out
/// of memory on a real client).
#[test]
fn narrowing_an_element_binding_checks_quickly() {
    for method in [
        "m() { const el = this.el; if (el) { return 1; } const p = this.parent; if (p) return 2; return 0; }",
        "m() { const p = this.el.parentElement; if (p !== null) { return 1; } return 0; }",
        "m(x) { if (x === this.el) { return 1; } return 0; }",
    ] {
        let mut src = vec!["export function mk(parent) {".to_string()];
        src.push("  const root = document.createElement('div');".to_string());
        let mut prev = "root".to_string();
        for i in 1..5 {
            src.push(format!(
                "  const d{i} = document.createElement('span'); d{i}.textContent = 'x'; \
                 {prev}.appendChild(d{i});"
            ));
            prev = format!("d{i}");
        }
        src.push("  parent.appendChild(root);".to_string());
        src.push(format!("  const o = {{ el: root, parent, {method} }};\n  return o;\n}}"));
        check_quickly(&src.join("\n"));
    }
}

fn nested_elements_class() -> String {
    let mut src = vec![
        "export class V {".to_string(),
        "  constructor(root) { this.root = root; }".to_string(),
        "  build() {".to_string(),
        "    const d0 = document.createElement('div');".to_string(),
    ];
    for i in 1..10 {
        src.push(format!(
            "    const d{i} = document.createElement('span'); d{i}.textContent = 'x'; \
             d{}.appendChild(d{i});",
            i % std::cmp::max(1, i / 2)
        ));
    }
    src.push("    this.root.appendChild(d0);\n  }\n}".to_string());
    src.join("\n")
}

/// Check `src` (it must have no errors) within the time bound.
fn check_quickly(src: &str) {
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
    assert!(
        elapsed < Duration::from_secs(10),
        "checking took {elapsed:?}: an element tree is written out in full again"
    );
}
