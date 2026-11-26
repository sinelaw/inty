//! The checked program as printed: a class as written, with an
//! annotation above each method that the checker reads back.

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
    /** Build the rows for `items`. */
    setItems(items) { this.items = items; return this.items.length; }
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
    assert!(
        out.contains(
            "    /** Build the rows for `items`. */\n    \
             /** function setItems<a>(items: a[]) => Number */\n    setItems(items) {"
        ),
        "{out}"
    );
    assert!(
        out.contains("/** function highlight<a>(i: Number, pointer: a) => Undefined */"),
        "{out}"
    );
    assert!(out.contains("/** function current<a>() => a */"), "{out}");
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
