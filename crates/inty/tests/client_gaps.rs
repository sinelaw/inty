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
