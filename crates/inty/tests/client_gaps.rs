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
