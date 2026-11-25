//! A function kept in a class's field and called as `this.f(…)`: the call
//! doesn't make it a method of the class. A function that uses no `this`
//! can be kept and called so by several classes.

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
fn shared_callback_does_not_unify_two_classes() {
    let r = check(
        "class Term {\n  constructor(app) { this.app = app; this.t = 1; }\n  \
         go() { return this.app().name; }\n}\n\
         class Panel {\n  constructor(app) { this.app = app; this.selected = []; }\n  \
         status() { return this.app().name.length + this.selected.length; }\n}\n\
         export function main() {\n  const getApp = () => ({ name: \"x\" });\n  \
         const p = new Panel(getApp);\n  const t = new Term(getApp);\n  \
         return p.status() + t.go().length;\n}\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn callback_passed_from_one_class_to_another() {
    let r = check(
        "class Term {\n  constructor(key) { this.key = key; }\n  go(e) { return this.key(e); }\n}\n\
         class Panel {\n  constructor(port) { this.say = port.say; this.key = port.key; }\n  \
         add() { const t = new Term(this.key); return t.go(1); }\n  \
         fail() { this.say(\"x\"); }\n}\n\
         const port = { say: (t) => { console.log(t); }, key: (e) => e > 0 };\n\
         export const p = new Panel(port);\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn declared_record_of_functions_in_a_field() {
    let r = check(
        "/** type Port = {say: (String) => Undefined} */\n\
         /** function mkPort() => Port */\n\
         function mkPort() { return { say: (t) => { console.log(t); } }; }\n\
         class Panel {\n  constructor() { this.port = mkPort(); }\n  \
         hello() { this.port.say(\"x\"); }\n}\n\
         export const p = new Panel();\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn sibling_method_reading_this_is_still_a_method() {
    let r = check(
        "class A {\n  constructor() { this.n = 2; }\n  a() { return this.b() + 1; }\n  \
         b() { return this.n; }\n}\nexport const r = new A().a();\n",
    );
    assert!(r.is_ok(), "{:?}", r);
}

#[test]
fn another_objects_method_is_not_a_callback() {
    // `o.m` reads `this` as `o`; `Term` calls it on a `Term`.
    let r = check(
        "class Term {\n  constructor(key) { this.key = key; }\n  go(e) { return this.key(e); }\n}\n\
         const o = { y: 2, m(e) { return this.y + e; } };\n\
         export const t = new Term(o.m);\n",
    );
    assert!(r.is_err(), "a method of another object must be rejected");
}

#[test]
fn callback_reading_the_instance_as_this_is_rejected() {
    // A callback whose `this` is the class's instance isn't typed: the
    // class's field holds a function that uses no `this`.
    let r = check(
        "class Term {\n  constructor(key) { this.key = key; this.x = 1; }\n  \
         go(e) { return this.key(e); }\n}\n\
         export const t = new Term(function (e) { return this.x + e; });\n",
    );
    assert!(r.is_err(), "a callback reading `this` must be rejected");
}
