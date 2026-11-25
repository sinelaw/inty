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
