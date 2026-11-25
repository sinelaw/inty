//! Narrowing a value read off a field inside a class method: the field's
//! type (set in the constructor) is known when the method is checked, so
//! a test on the value narrows it as it does in a plain function.

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

const PRELUDE: &str = "/** type Item = {n: Number} */\n\
/** function noItems() => Map<String, Item> */\n\
function noItems() { return new Map(); }\n";

fn method(body: &str) -> String {
    format!(
        "{PRELUDE}export class C {{\n  constructor() {{ this.items = noItems(); }}\n  \
         a(k) {{ const x = this.items.get(k); {body} }}\n}}\n"
    )
}

#[test]
fn ternary_narrows_in_class_method() {
    let r = check(&method("return x !== undefined ? x.n : 0;"));
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn early_return_narrows_in_class_method() {
    let r = check(&method("if (x === undefined) return 0; return x.n;"));
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn and_chain_narrows_in_class_method() {
    let r = check(&method("return x !== undefined && x.n > 0;"));
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn loop_conditions_narrow_in_class_method() {
    let r = check(&method(
        "let s = 0; while (x !== undefined && s < x.n) s++; \
         for (; x !== undefined && s < x.n; s++) {} return s;",
    ));
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn unnarrowed_read_in_class_method_still_rejected() {
    let r = check(&method("return x.n;"));
    assert!(
        r.is_err(),
        "reading `n` off `Item | Undefined` must be rejected"
    );
}
