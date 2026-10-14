//! The Lean model on programs of several modules (`lean/ROADMAP.md`, phase
//! 7): `inty::model_wire::lower_entry` writes a program with the modules
//! its entry imports as one wire line, each module running once, in the
//! order JavaScript runs them, an import being the exporting module's
//! binding itself. inty checks the same files as the CLI does
//! (`inty::modules::check_module`); the two must agree on accepting each
//! program, and the model's value must be the one JavaScript gives.

use inty::builtins::initial_env;
use inty::infer::InferState;
use std::path::{Path, PathBuf};
use std::process::Command;

mod oracle;
use oracle::*;

/// A program: its files, the first the entry, and the model's value if
/// both accept it.
struct Case {
    what: &'static str,
    files: &'static [(&'static str, &'static str)],
    value: Option<&'static str>,
}

const CASES: &[Case] = &[
    Case {
        what: "a named import, a new instance at each use",
        files: &[
            (
                "main.js",
                "import { id } from \"./lib.js\"; id(1) - 1; id(\"s\").length;",
            ),
            ("lib.js", "export function id(x) { return x; }"),
        ],
        value: Some("num 1"),
    },
    Case {
        what: "a namespace's members, a new instance at each use",
        files: &[
            (
                "main.js",
                "import * as L from \"./lib.js\"; L.id(2) - 1; L.id(\"ab\").length;",
            ),
            ("lib.js", "export function id(x) { return x; }"),
        ],
        value: Some("num 2"),
    },
    Case {
        what: "default exports, of a function and of a value",
        files: &[
            (
                "main.js",
                "import g from \"./greet.js\"; import v from \"./version.js\"; g(v);",
            ),
            (
                "greet.js",
                "export default function greet(n) { return n + 1; }",
            ),
            ("version.js", "export default 3;"),
        ],
        value: Some("num 4"),
    },
    Case {
        what: "an export list, renaming",
        files: &[
            (
                "main.js",
                "import { square, pow3 } from \"./math.js\"; square(2) + pow3(2);",
            ),
            (
                "math.js",
                "function square(n) { return n * n; } function cube(n) { return n * n * n; } \
                 export { square, cube as pow3 };",
            ),
        ],
        value: Some("num 12"),
    },
    Case {
        what: "an exported `let` is live",
        files: &[
            (
                "main.js",
                "import { count, inc } from \"./store.js\"; inc(); inc(); count;",
            ),
            (
                "store.js",
                "export let count = 0; export function inc() { count = count + 1; }",
            ),
        ],
        value: Some("num 2"),
    },
    Case {
        what: "an exported object, shared",
        files: &[
            (
                "main.js",
                "import { state, bump } from \"./store.js\"; bump(); state.count;",
            ),
            (
                "store.js",
                "export let state = {count: 0}; \
                 export function bump() { state.count = state.count + 1; }",
            ),
        ],
        value: Some("num 1"),
    },
    Case {
        what: "re-exports: named, the default, a namespace",
        files: &[
            (
                "main.js",
                "import describe, { double, internals } from \"./lib.js\"; \
                 double(2) + internals.TAG.length + describe().length;",
            ),
            (
                "lib.js",
                "export { double } from \"./internal.js\"; \
                 export { default } from \"./internal.js\"; \
                 export * as internals from \"./internal.js\";",
            ),
            (
                "internal.js",
                "export function double(n) { return n + n; } export const TAG = \"t\"; \
                 export default function describe() { return TAG; }",
            ),
        ],
        value: Some("num 6"),
    },
    Case {
        what: "`export *`",
        files: &[
            (
                "main.js",
                "import { double, TAG } from \"./lib.js\"; double(TAG.length);",
            ),
            ("lib.js", "export * from \"./internal.js\";"),
            (
                "internal.js",
                "export function double(n) { return n + n; } export const TAG = \"t\";",
            ),
        ],
        value: Some("num 2"),
    },
    Case {
        what: "mutually recursive exports",
        files: &[
            (
                "main.js",
                "import { isEven } from \"./even.js\"; isEven(10);",
            ),
            (
                "even.js",
                "export function isEven(n) { return n === 0 ? true : isOdd(n - 1); } \
                 export function isOdd(n) { return n === 0 ? false : isEven(n - 1); }",
            ),
        ],
        value: Some("bool true"),
    },
    Case {
        what: "a module imported twice runs once",
        files: &[
            (
                "main.js",
                "import { a } from \"./a.js\"; import { b } from \"./b.js\"; a + b;",
            ),
            (
                "a.js",
                "import { tick } from \"./c.js\"; export const a = tick();",
            ),
            (
                "b.js",
                "import { tick } from \"./c.js\"; export const b = tick();",
            ),
            (
                "c.js",
                "export let n = 0; export function tick() { n = n + 1; return n; }",
            ),
        ],
        value: Some("num 3"),
    },
    Case {
        what: "an export's type, checked at its use",
        files: &[
            ("main.js", "import { dec } from \"./lib.js\"; dec(\"s\");"),
            ("lib.js", "export function dec(n) { return n - 1; }"),
        ],
        value: None,
    },
    Case {
        what: "an exported `let`, one type for its importers",
        files: &[
            (
                "main.js",
                "import { cell, set } from \"./cell.js\"; set(1); set(\"s\");",
            ),
            (
                "cell.js",
                "export let cell = []; export function set(x) { cell[0] = x; }",
            ),
        ],
        value: None,
    },
];

/// Whether inty accepts the program whose entry is `path`, as the CLI
/// checks it.
fn inty_accepts(path: &Path) -> bool {
    let path = path.to_path_buf();
    inty::worker::run_with_inference_stack("inty-modules", move || {
        let mut state = InferState::new();
        inty::modules::check_module(&mut state, initial_env(), &path).is_ok()
            && state.take_errors().is_empty()
            && state.resolve_constraints().is_ok()
    })
}

fn write_case(dir: &Path, case: &Case) -> PathBuf {
    std::fs::create_dir_all(dir).unwrap();
    for (name, text) in case.files {
        std::fs::write(dir.join(name), text).unwrap();
    }
    dir.join(case.files[0].0)
}

#[test]
fn the_model_on_programs_of_several_modules() {
    let root = std::env::temp_dir().join(format!("inty-model-modules-{}", std::process::id()));
    let mut lowered = Vec::new();
    for (i, case) in CASES.iter().enumerate() {
        let entry = write_case(&root.join(i.to_string()), case);
        let wire = inty::model_wire::lower_entry(&entry)
            .unwrap_or_else(|e| panic!("{}: not in the fragment: {e}", case.what));
        lowered.push((case, entry, wire));
    }
    let Some(model) = model_path() else {
        assert!(
            std::env::var_os("INTY_REQUIRE_MODEL").is_none(),
            "no inty-model, and INTY_REQUIRE_MODEL is set"
        );
        eprintln!("skipping: no inty-model (cd lean && lake build)");
        return;
    };
    let input: String = lowered.iter().map(|(_, _, w)| format!("{w}\n")).collect();
    let lines = run_lines(Command::new(model), "inty-model", input, lowered.len());
    let mut failures = Vec::new();
    for ((case, entry, wire), line) in lowered.iter().zip(&lines) {
        let (typing, run) = parse_model_line(line);
        let model = typing != Typing::Reject;
        let inty = inty_accepts(entry);
        if model != inty || model != case.value.is_some() {
            failures.push(format!(
                "{}: inty {}, the model {}\n  wire: {wire}\n  model: {line}",
                case.what,
                if inty { "accepts" } else { "rejects" },
                if model { "accepts" } else { "rejects" },
            ));
        } else if let Some(v) = case.value {
            // (The model prints a number by its bits.)
            let v = match v.strip_prefix("num ") {
                Some(n) => format!("num {}", n.parse::<f64>().unwrap().to_bits()),
                None => v.to_string(),
            };
            if run != Run::Value(v.clone()) {
                failures.push(format!(
                    "{}: the model's value is {run:?}, not {v}",
                    case.what
                ));
            }
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Programs whose lowering would change their meaning, left out.
#[test]
fn programs_of_several_modules_the_model_leaves_out() {
    let cases: &[(&str, &[(&str, &str)])] = &[
        (
            "an assignment to an import (read-only in JavaScript)",
            &[
                ("main.js", "import { n } from \"./lib.js\"; n = 2;"),
                ("lib.js", "export let n = 1;"),
            ],
        ),
        (
            "an imported `let` taken apart by a test, which its module assigns",
            &[
                (
                    "main.js",
                    "import { x, clear } from \"./lib.js\"; \
                     const f = x != null ? () => { clear(); return x - 1; } : () => 0; f();",
                ),
                (
                    "lib.js",
                    "/** export let x: Number | Null */ export let x = 1; \
                     export function clear() { x = null; }",
                ),
            ],
        ),
        (
            "a cycle of imports",
            &[
                ("main.js", "import { a } from \"./a.js\"; a;"),
                ("a.js", "import { b } from \"./b.js\"; export const a = 1;"),
                ("b.js", "import { a } from \"./a.js\"; export const b = 2;"),
            ],
        ),
        (
            "a builtin module",
            &[("main.js", "import { readFileSync } from \"node:fs\"; 1;")],
        ),
        (
            "an import of what isn't exported",
            &[
                ("main.js", "import { hidden } from \"./lib.js\"; hidden;"),
                ("lib.js", "const hidden = 1;"),
            ],
        ),
    ];
    let root = std::env::temp_dir().join(format!("inty-model-modules-out-{}", std::process::id()));
    let mut failures = Vec::new();
    for (i, (what, files)) in cases.iter().enumerate() {
        let dir = root.join(i.to_string());
        std::fs::create_dir_all(&dir).unwrap();
        for (name, text) in files.iter() {
            std::fs::write(dir.join(name), text).unwrap();
        }
        match inty::model_wire::lower_entry(&dir.join(files[0].0)) {
            Ok(wire) => failures.push(format!("{what}: lowered to {wire}")),
            Err(why) => eprintln!("{what}: {why}"),
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
