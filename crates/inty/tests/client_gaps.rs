//! Gaps found type-checking a real JavaScript client: builtins and
//! inference rules that were missing a case another path already had.

use inty::frontends::javascript::parse;
use inty::stdlib::initial_env_with_stdlib;

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

/// `for (const [k, v] of m)` with `m` not known at the loop: the tuple's
/// components are read once it is (`Indexable` on a tuple), as when it is.
#[test]
fn destructuring_entries_of_a_map_known_later() {
    let ok = "export function f(m) { let s = 0; for (const [k, v] of m) s += v + k.length; return s; }\n\
              /** const mm: Map<String, Number> */\nconst mm = new Map();\nexport const r = f(mm);\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
    let bad = "export function f(m) { let s = 0; for (const [k, v] of m) s += v + k.length; return s; }\n\
               /** const mm: Map<String, String> */\nconst mm = new Map();\nexport const r = f(mm);\n";
    assert!(
        check(bad).is_err(),
        "the value is a String, added to a Number"
    );
    let short = "function g(p) { const [a, b, c] = p; return a; }\n\
                 /** const q: [Number, String] */\nconst q = [1, \"a\"];\nexport const r = g(q);\n";
    assert!(check(short).is_err(), "a pair has no third component");
}

/// `xs.flat()` on an array of arrays is one array of their elements.
#[test]
fn array_flat() {
    let ok = "export const a = [[1], [2, 3]].flat();\nexport const b = a[0] + 1;\n\
              export function f(xs) { return xs.flat(); }\nexport const r = f([[\"a\"]])[0].length;\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
    // Not an array of arrays: `flat` would keep the elements as they are,
    // which the one-level type doesn't say.
    assert!(check("export const a = [1, 2].flat();\n").is_err());
    // A depth changes the result's type with the number: not taken.
    assert!(check("export const a = [[1]].flat(2);\n").is_err());
}

/// A regular expression's type, printed `RegExp`, is named so in
/// annotations too.
#[test]
fn regexp_names_a_type() {
    let ok = "/** function f(re: RegExp) => Boolean */\n\
              export function f(re) { return re.test(\"a\"); }\nexport const r = f(/a/);\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
    let bad = "/** function f(re: RegExp) => Boolean */\n\
               export function f(re) { return re.test(\"a\"); }\nexport const r = f(\"a\");\n";
    assert!(check(bad).is_err(), "a string isn't a RegExp");
}

/// `return p` in an `async` function, `p` a promise: the function's
/// promise resolves to `p`'s value (not to `p`), as `then`'s callback's
/// does, whether or not `p`'s type is known at the `return`.
#[test]
fn async_return_of_a_promise_is_its_value() {
    let ok = "async function inner(x) { return { path: x }; }\n\
              export async function outer(p) { if (p === \"\") return { path: \"a\" }; return inner(p); }\n\
              export async function use() { const r = await outer(\"a\"); return r.path.length; }\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
    // The method returned is checked after the one returning its promise.
    let later = "export class S {\n  constructor() { this.buffers = new Map(); }\n  \
                 async load(abs) { const b = [...this.buffers.values()].find((x) => x.path === abs); \
                 if (b) return b; return this.adopt({ path: abs }); }\n  \
                 async adopt(d) { const b = { path: d.path }; this.buffers.set(d.path, b); return b; }\n}\n";
    assert!(check(later).is_ok(), "{:?}", check(later));
    // A value and a promise of another type still disagree.
    let bad = "async function inner() { return 1; }\n\
               export async function outer(p) { if (p) return \"a\"; return inner(); }\n";
    assert!(check(bad).is_err());
}

/// A call fills or skips a declared optional parameter for itself only,
/// leaving the function's type as it was: one canvas context's `arc` is
/// called with and without `ccw`.
#[test]
fn optional_parameter_filled_or_skipped_per_call() {
    let ok = "const c = document.createElement(\"canvas\");\nconst ctx = c.getContext(\"2d\");\n\
              if (ctx) { ctx.arc(1, 2, 3, 0, 1); ctx.arc(1, 2, 3, 0, 1, true); ctx.arc(0, 0, 1, 0, 2); }\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
    // A callback the function passes to `map` (which may give it an
    // index) and calls with one argument: a callback needing the index
    // is still rejected, as the call decides the parameter where the
    // function is generalised.
    let bad = "export function f(cb) { [1].map(cb); cb(1); }\nf((x, i) => i.toFixed());\n";
    assert!(check(bad).is_err());
}

/// Review of #116: linking two variables unification showed equal must
/// not link through an arm that accepts types that differ (here a
/// method, which reads `this`, against `Math.abs`, declared without a
/// `this`): the method kept in `xs` stays a method.
#[test]
fn linking_keeps_a_method_a_method() {
    let src = "const o = { n: 1, m(x) { return this.n + x; } };\n\
               const xs = []; xs.push(o.m);\nconst ys = []; ys.push(Math.abs);\n\
               const zs = [xs, ys];\nconst h = xs[0];\nh(1);\n";
    assert!(
        check(src).is_err(),
        "h is a method: calling it detached is rejected"
    );
}

/// Review of #116: what a waiting `return` of an async function gives its
/// promise isn't generalised before the returned type is known.
#[test]
fn async_return_waiting_is_not_generalised() {
    let src = "function outer() {\n  const cell = [];\n  async function f() { return cell[0]; }\n  \
               cell.push(Promise.resolve(1));\n  const r = f();\n  r.then(x => x.foo.bar);\n}\nouter();\n";
    assert!(
        check(src).is_err(),
        "the promise holds a Number, which has no `foo`"
    );
    let ok = "function outer() {\n  const cell = [];\n  async function f() { return cell[0]; }\n  \
              cell.push(Promise.resolve(1));\n  const r = f();\n  r.then(x => x + 1);\n}\nouter();\n";
    assert!(check(ok).is_ok(), "{:?}", check(ok));
}

/// Two instances of one declared union whose record arm has optional
/// fields (each instance its own presence variables) are the same type:
/// unified member by member. They were compared as sets of syntactically
/// equal members, and rejected ("expected 'Boolean | {p?: Boolean}',
/// found 'Boolean | {p?: Boolean}'").
#[test]
fn instances_of_one_union_unify() {
    let src = "/** function mk() => {o: Boolean | {p?: Boolean, q?: Number}} */\n\
               function mk() { return {o: true}; }\n\
               const a = mk(); const b = mk(); const xs = [a, b];\n";
    let r = check(src);
    assert!(r.is_ok(), "{:?}", r);
    // Members of different kinds still don't unify.
    let bad = "/** function f() => Boolean | {p?: Boolean} */\nfunction f() { return true; }\n\
               /** function g() => Number | {p?: Boolean} */\nfunction g() { return 1; }\n\
               const xs = [f(), g()];\n";
    assert!(check(bad).is_err());
}

/// An optional parameter a call skipped, on an object a generalised
/// function reaches, stays open rather than being decided by that call,
/// so the same object's later calls may pass it.
#[test]
fn optional_parameter_reached_by_generalisation_stays_open() {
    let src = "class P {\n  constructor() { this.a = document.createElement(\"div\"); }\n  \
               one() { this.a.addEventListener(\"x\", (e) => {}); }\n  \
               two() { this.a.addEventListener(\"wheel\", (e) => {}, { passive: false }); }\n}\n\
               export const p = new P();\n";
    let r = check(src);
    assert!(r.is_ok(), "{:?}", r);
}
