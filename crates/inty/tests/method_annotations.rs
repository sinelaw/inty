//! An annotation written above a method (`/** function m(x: T) => R */`)
//! types it, as one above a function declaration does: the body is
//! checked against it and callers see its type. Its `this` is the one
//! the class or object gives the method, unless it says (`this: T`).

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

#[test]
fn a_class_method_body_is_checked_against_its_annotation() {
    let r = check(
        "class P {\n  /** function open(x: String) => Number */\n  open(x) { return x; }\n}\n",
    );
    assert!(r.is_err(), "a String returned where Number is declared");
}

#[test]
fn a_class_method_call_is_checked_against_its_annotation() {
    let ok = "class P {\n  /** function open(x: String) => Number */\n  open(x) { return x.length; }\n}\n";
    assert!(check(&format!("{ok}new P().open(\"a\");\n")).is_ok());
    // Without the annotation, `open(1)` would fail only inside the body
    // (`length` of a number); with it, at the argument.
    let r = check(&format!("{ok}new P().open(1);\n"));
    assert!(r.as_ref().is_err_and(|e| e.contains("String")), "{:?}", r);
    // The result is the declared one.
    let r = check(&format!(
        "{ok}const n = new P().open(\"a\");\n/** const s: String */\nconst s = n;\n"
    ));
    assert!(r.is_err());
}

#[test]
fn an_annotated_method_using_this_keeps_the_instance_as_this() {
    let r = check(
        "class P {\n  constructor() { this.k = 1; }\n  \
         /** function open(x: String) => Number */\n  \
         open(x) { return x.length + this.k; }\n}\n\
         new P().open(\"a\");\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn an_async_method_is_checked_against_its_annotation() {
    let src = |ret: &str| {
        format!(
            "class P {{\n  /** function open(x: String) => {ret} */\n  \
             async open(x) {{ return x.length; }}\n}}\n"
        )
    };
    assert!(check(&src("Promise<Number>")).is_ok());
    assert!(check(&src("Promise<String>")).is_err());
}

#[test]
fn an_object_literal_method_is_checked_against_its_annotation() {
    let r = check(
        "const o = {\n  /** function open(x: String) => Number */\n  open(x) { return x; },\n};\n",
    );
    assert!(r.is_err());
    let r = check(
        "const o = {\n  /** function open(x: String) => Number */\n  \
         open(x) { return x.length; },\n};\no.open(1);\n",
    );
    assert!(r.as_ref().is_err_and(|e| e.contains("String")), "{:?}", r);
}

#[test]
fn an_annotation_goes_to_the_method_it_names() {
    // An annotation naming another method isn't the next method's.
    let r = check(
        "class P {\n  /** function other(x: String) => String */\n  \
         open(x) { return x.length; }\n  other(x) { return x; }\n}\n\
         new P().open(1);\n",
    );
    assert!(r.is_err(), "`open` is unannotated, so `1.length` fails");
    let r = check(
        "class P {\n  open(x) { return x; }\n  \
         /** function other(x: String) => String */\n  other(x) { return x; }\n}\n\
         new P().open(1);\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}
