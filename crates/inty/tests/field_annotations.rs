//! `/** this.x: T */` above a constructor's `this.x = …` line: the field's
//! type, as `/** const x: T */` is a binding's. The value set there is
//! checked against it (and so a constructor parameter that flows into it),
//! and the class names the field's type rather than a parameter for it.

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

const LINES: &str = "class Lines {\n  constructor(starts) {\n    \
                     /** this.starts: Number[] */\n    this.starts = starts;\n  }\n  \
                     count() { return this.starts.length; }\n}\n";

#[test]
fn an_annotated_field_fixes_its_type_and_the_parameter_that_sets_it() {
    // The class takes no type argument: `starts` is a `Number[]`.
    let r = check(&format!(
        "{LINES}/** function f(l: Lines) => Number */ function f(l) {{ return l.count(); }}\n\
         const n = f(new Lines([1, 2]));\n"
    ));
    assert!(r.is_ok(), "{:?}", r);
    // The constructor's parameter is what the field is.
    let r = check(&format!("{LINES}const l = new Lines([\"a\"]);\n"));
    assert!(r.is_err(), "a String[] isn't a Number[]");
    // The value set is checked against the annotation.
    let r = check(
        "class C {\n  constructor() {\n    /** this.n: Number */\n    this.n = \"x\";\n  }\n}\n",
    );
    assert!(r.is_err(), "a String isn't a Number");
}

#[test]
fn a_field_annotation_may_say_more_than_its_first_value() {
    let r = check(
        "class C {\n  constructor(a) {\n    /** this.x: String | Null */\n    this.x = null;\n  }\n  \
         /** method get() => String | Null */\n  get() { return this.x; }\n}\n\
         /** function f(c: C) => Number */ function f(c) { return (c.get() ?? \"\").length; }\n",
    );
    assert!(r.is_ok(), "{:?}", r);
    // Each value the constructor sets it to fits it.
    let r = check(
        "class C {\n  constructor(a) {\n    /** this.x: String | Null */\n    this.x = null;\n    \
         this.x = a;\n  }\n}\nconst c = new C(1);\n",
    );
    assert!(r.is_err(), "a Number isn't a String | Null");
    // The margin-led form too.
    let r = check(
        "class C {\n  constructor(a) {\n    /**\n     * this.x: String\n     */\n    \
         this.x = a;\n  }\n}\nconst c = new C(1);\n",
    );
    assert!(r.is_err(), "a Number isn't a String");
}

#[test]
fn a_field_annotation_anywhere_else_is_an_error() {
    for (what, src) in [
        (
            "a statement between it and the line",
            "class C {\n  constructor(s) {\n    /** this.s: Number[] */\n    const k = 1;\n    \
             this.s = s;\n  }\n}\n",
        ),
        (
            "in a method",
            "class C {\n  constructor(s) { this.s = s; }\n  \
             set(x) {\n    /** this.s: Number[] */\n    this.s = x;\n  }\n}\n",
        ),
        (
            "another field's line",
            "class C {\n  constructor(s) {\n    /** this.t: Number */\n    this.s = s;\n  }\n}\n",
        ),
        (
            "annotated twice",
            "class C {\n  s: Number[];\n  constructor(s) {\n    /** this.s: Number[] */\n    \
             this.s = s;\n  }\n}\n",
        ),
    ] {
        assert!(check(src).is_err(), "{what}:\n{src}");
    }
}

#[test]
fn a_doc_comment_starting_with_this_is_prose() {
    let r = check(
        "class C {\n  constructor(s) {\n    /** this keeps the count */\n    this.n = s + 0;\n  }\n}\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}
