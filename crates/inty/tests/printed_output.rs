//! The checked program as printed (`inty file.js`): it reads back, as
//! JavaScript and in each annotation, and checks as written. A class is
//! printed as written, with an annotation above each method.

use inty::ast::pretty::print_program_with;
use inty::frontends::javascript::parse;
use inty::infer::decorate_with_classes;
use inty::stdlib::initial_env_with_stdlib;

fn print(src: &str) -> String {
    let program = parse(src).unwrap();
    let (env, mut state) = initial_env_with_stdlib().unwrap();
    let (_, env) = state.infer_program_with_env(&env, &program).unwrap();
    state.resolve_constraints().unwrap();
    assert!(state.take_errors().is_empty());
    let (decorated, classes) = decorate_with_classes(&program, &env, &state, src);
    print_program_with(&decorated, classes)
}

fn checks(src: &str) -> bool {
    let program = parse(src).unwrap();
    let (env, mut state) = initial_env_with_stdlib().unwrap();
    state.infer_program_with_env(&env, &program).is_ok()
        && state.resolve_constraints().is_ok()
        && state.take_errors().is_empty()
}

const MENU: &str = "class Menu {
    constructor(el) { this.el = el; this.items = []; this.sel = 0; }
    setItems(items) { this.items = items; return this.items.length; }
    /** Move the selection. */
    select(n) { this.sel = n; return n + 1; }
    highlight(i, pointer) { if (pointer) { this.sel = i; } }
    current() { return this.items[this.sel]; }
    chain() { return this; }
    async fetchAll(url, opt = 1) { return [url, opt]; }
}
";

#[test]
fn a_class_is_printed_as_written_with_its_methods_annotated() {
    let out = print(MENU);
    assert!(out.starts_with("class Menu {\n"), "{out}");
    // Above its documentation comment's method, after the comment.
    assert!(
        out.contains(
            "    /** Move the selection. */\n    \
             /** function select(n: Number) => Number */\n    select(n) {"
        ),
        "{out}"
    );
    // Methods whose types have type variables (the class's, the same at
    // every call on an instance) have none: a method's annotation can't.
    assert!(!out.contains("function setItems"), "{out}");
    assert!(!out.contains("function highlight"), "{out}");
    assert!(!out.contains("function current"), "{out}");
    assert!(
        out.contains("/** function fetchAll(url: Number, opt: Number) => Promise<Number[]> */"),
        "{out}"
    );
    // A method returning `this` has none: its class's type can't be
    // written out.
    assert!(out.contains("}\n    chain() { return this; }"), "{out}");
}

#[test]
fn a_printed_class_checks_as_written() {
    let out = print(MENU);
    assert!(checks(&out), "{out}");
}

#[test]
fn an_annotated_method_keeps_its_annotation() {
    let src = "class P {\n  /** function open(x: String) => Number */\n  open(x) { return x.length; }\n}\n";
    let out = print(src);
    assert_eq!(out.matches("/** function open").count(), 1, "{out}");
}

#[test]
fn an_exported_class_is_printed_as_written() {
    let out = print("export class P {\n  go(x) { return x * 2; }\n}\n");
    assert!(
        out.starts_with("export class P {\n  /** function go(x: Number) => Number */\n  go(x)"),
        "{out}"
    );
}

/// The printed program checks as written, and prints the same again.
fn reads_back(src: &str) -> String {
    let out = print(src);
    assert!(checks(&out), "{out}");
    out
}

#[test]
fn an_instance_is_annotated_by_its_class_name() {
    let out = reads_back(
        "function make() {\n  class Inner { go(x) { return x * 2; } }\n  return new Inner();\n}\n",
    );
    assert!(out.contains("/** function make() => Inner */"), "{out}");
}

#[test]
fn a_declaration_without_a_value_has_no_annotation() {
    // `/** var x: T */ var x;` would declare a constant defined elsewhere.
    let out = reads_back("function f() {\n  var x, y;\n  x = 1; y = 2;\n  return x + y;\n}\n");
    assert!(!out.contains("var x:"), "{out}");
}

#[test]
fn async_functions_and_arrows_are_printed_as_written() {
    let out = reads_back(
        "async function f(p) { const v = await p; return v + 1; }\n\
         const g = async (x) => x;\n\
         const o = { n: 1, get() { return [1].map((i) => i + this.n); } };\n",
    );
    assert!(out.contains("async function f(p)"), "{out}");
    assert!(out.contains("async (x) =>"), "{out}");
    assert!(out.contains("(i) =>"), "{out}");
}

#[test]
fn type_aliases_are_printed() {
    let out = reads_back(
        "/** type Status = \"ok\" | \"err\" */\n\
         /** function color(s: Status) => String */\n\
         function color(s) { return s === \"ok\" ? \"green\" : \"red\"; }\n",
    );
    assert!(
        out.starts_with("/** type Status = \"ok\" | \"err\" */\n"),
        "{out}"
    );
}

#[test]
fn a_type_that_would_read_back_as_another_is_left_out() {
    // A method taking a callback the class leaves open (`{(…) => R | a}`,
    // an open record) has no annotation: written out, it would read as a
    // callback returning `R | a`.
    let out = reads_back(
        "class Menu {\n  constructor() { this.items = [{ label: \"a\" }]; }\n  \
         each(f) { this.items.forEach(f); }\n}\n",
    );
    assert!(!out.contains("function each"), "{out}");
}

#[test]
fn a_function_reading_this_reads_back() {
    // Its `this` (`{x: …}`, or a variable constrained to have `x`) can't
    // be written in its annotation, which would then say it uses none.
    reads_back("const f = function () { return this.x + 1; };\nconst o = {x: 1, f: f};\no.f();\n");
    reads_back("function getX() { return this.x; }\nconst o = {x: 1, getX: getX};\no.getX();\n");
}

#[test]
fn an_object_literal_methods_annotation_is_printed() {
    let out = reads_back(
        "function mk() {\n  return {\n    /** function open(x: String) => Number | String */\n    \
         open(x) { return x.length; },\n  };\n}\n",
    );
    assert!(
        out.contains("/** function open(x: String) => Number | String */ open(x)"),
        "{out}"
    );
}

#[test]
fn a_promise_written_out_is_not_printed_as_async() {
    let out = reads_back(
        "function sync() { return Promise.resolve((() => { throw new Error(\"x\"); })()); }\n",
    );
    assert!(!out.contains("async"), "{out}");
}

#[test]
fn a_private_method_has_no_annotation() {
    let out = reads_back(
        "class P {\n  #twice(x) { return x * 2; }\n  go() { return this.#twice(1); }\n}\n",
    );
    assert_eq!(out.matches("/** function").count(), 1, "{out}");
    assert!(out.contains("/** function go() => Number */"), "{out}");
}

#[test]
fn a_default_exported_class_has_its_methods_annotated() {
    let out = reads_back("export default class {\n  a(x) { return x + 1; }\n}\n");
    assert!(
        out.contains("/** function a(x: Number) => Number */"),
        "{out}"
    );
}

#[test]
fn annotations_keep_the_sources_line_endings() {
    let out = print("class P {\r\n  a(x) { return x + 1; }\r\n}\r\n");
    assert!(
        out.contains("  /** function a(x: Number) => Number */\r\n  a(x)"),
        "{out:?}"
    );
}
