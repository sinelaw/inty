//! What the differential and corpus tests share: inty's verdicts (its type
//! and its interpreter's), the model's, and a JavaScript engine's, in the
//! model's wire format.
#![allow(dead_code)]

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use inty::dynamics::{run_to_end_with_fuel, Stuck, Value};
use inty::types::{LitValue, Nothing, Type};

/// inty's verdict on a program, in the model's terms.
#[derive(Clone, Debug, PartialEq)]
pub enum Typing {
    Type(String),
    Reject,
}

/// An interpreter's verdict.
#[derive(Clone, Debug, PartialEq)]
pub enum Run {
    Value(String),
    /// An uncaught `throw` of this value.
    Thrown(String),
    /// A `return` that escaped to the top (the model only; typing rules it out).
    Returned(String),
    Stuck(String),
    /// A fault the type system allows, such as an index out of bounds.
    Fault(String),
    Timeout,
    Unsupported,
    /// The engine raised its own error (a `TypeError`, say).
    NativeError(String),
    /// The engine hit a resource limit: its stack, a string's length, time.
    Limit,
}

pub fn core_type(t: &Type) -> String {
    match t {
        Type::Number | Type::Literal(LitValue::Number(_)) => "number".into(),
        Type::String | Type::Literal(LitValue::String(_)) => "string".into(),
        Type::Boolean | Type::Literal(LitValue::Bool(_)) => "boolean".into(),
        Type::Undefined => "undefined".into(),
        Type::Null => "null".into(),
        Type::Func { .. } => "fun".into(),
        Type::Row(_) if t.as_callable().is_some() => "fun".into(),
        Type::Row(_) => "obj".into(),
        Type::Array(_) => "array".into(),
        Type::Maybe(Nothing::Null, _) => "nullable".into(),
        Type::Maybe(Nothing::Undefined, _) => "optional".into(),
        Type::Var(_) => "var".into(),
        // The empty union: what doesn't complete, such as a `throw`.
        Type::Union(ts) if ts.is_empty() => "never".into(),
        Type::Union(ts) => {
            let parts: Vec<String> = ts.iter().map(core_type).collect();
            // A union of different heads: a sum told apart by `typeof`,
            // as the model prints it.
            if parts.iter().all(|p| p == &parts[0]) {
                parts[0].clone()
            } else {
                "union".into()
            }
        }
        other => format!("other({})", other),
    }
}

pub fn number_wire(n: f64) -> String {
    // One NaN, whatever its payload.
    let n = if n.is_nan() { f64::NAN } else { n };
    format!("num {}", n.to_bits())
}

pub fn value_wire(v: Value) -> String {
    match v {
        Value::Number(n) => number_wire(n),
        Value::String(s) => format!("str s:{}", escape(&s)),
        Value::Boolean(v) => format!("bool {}", v),
        Value::Undefined => "undef".into(),
        Value::Null => "null".into(),
        Value::Closure(_) | Value::Builtin(_) => "fun".into(),
        Value::Object(_) => "obj".into(),
        Value::Array(_) => "arr".into(),
        other => format!("other {}", other),
    }
}

pub fn inty_run(program: &inty::ast::Program) -> Run {
    match run_to_end_with_fuel(program, 1_500) {
        Ok(v) => Run::Value(value_wire(v)),
        Err(Stuck::UncaughtThrow(v)) => Run::Thrown(value_wire(v)),
        Err(Stuck::FuelExhausted) => Run::Timeout,
        Err(Stuck::OutOfBounds { .. }) => Run::Fault("outOfBounds".into()),
        // Spreading what isn't an object: JavaScript copies a primitive's
        // own properties, which the model and `dynamics` don't.
        Err(Stuck::NotImplemented(what)) if what.contains("spread") => {
            Run::Stuck("notSpreadable".into())
        }
        Err(Stuck::NotImplemented(_)) => Run::Unsupported,
        Err(Stuck::UndefinedVariable(_)) => Run::Stuck("undefinedVariable".into()),
        // `new` on an arrow function: the model gets stuck calling what
        // `Value.asCtor` gives for it, which isn't callable.
        Err(Stuck::NotCallable(_)) | Err(Stuck::NotConstructor) => Run::Stuck("notCallable".into()),
        Err(Stuck::TypeMismatch { .. }) => Run::Stuck("typeMismatch".into()),
        Err(Stuck::ArityMismatch { .. }) => Run::Stuck("arityMismatch".into()),
        Err(Stuck::NotIndexable(_)) => Run::Stuck("notIndexable".into()),
        Err(Stuck::PropertyNotFound { .. }) => Run::Stuck("propertyNotFound".into()),
        Err(Stuck::BadAssignmentTarget) => Run::Stuck("badAssignmentTarget".into()),
        Err(Stuck::ReadOnly) => Run::Stuck("readOnly".into()),
    }
}

/// An interpreter's verdict in the model's wire format (`value V`,
/// `thrown V`, ...), as both the model and the engine print it.
pub fn parse_run(run: &str) -> Run {
    // Canonicalise NaN the same way as inty's side.
    let value = |v: &str| match v.strip_prefix("num ") {
        Some(bits) => number_wire(f64::from_bits(bits.parse().expect(run))),
        None => v.to_string(),
    };
    if run == "timeout" {
        Run::Timeout
    } else if run == "limit" {
        Run::Limit
    } else if let Some(v) = run.strip_prefix("value ") {
        Run::Value(value(v))
    } else if let Some(v) = run.strip_prefix("thrown ") {
        Run::Thrown(value(v))
    } else if let Some(v) = run.strip_prefix("returned ") {
        Run::Returned(value(v))
    } else if let Some(why) = run.strip_prefix("fault ") {
        Run::Fault(why.to_string())
    } else if let Some(name) = run.strip_prefix("error ") {
        Run::NativeError(name.to_string())
    } else {
        Run::Stuck(run.strip_prefix("stuck ").expect(run).to_string())
    }
}

pub fn parse_model_line(line: &str) -> (Typing, Run) {
    let (typing, run) = line
        .split_once(';')
        .unwrap_or_else(|| panic!("bad model line: {line}"));
    let typing = match typing {
        "reject" => Typing::Reject,
        t => Typing::Type(t.strip_prefix("type ").expect(line).to_string()),
    };
    (typing, parse_run(run))
}

/// Run a process on one line per input, and read its one line per input.
pub fn run_lines(mut command: Command, what: &str, input: String, n: usize) -> Vec<String> {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("start {what}: {e}"));
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || {
        stdin.write_all(input.as_bytes()).unwrap();
    });
    let out: Vec<String> = BufReader::new(child.stdout.take().unwrap())
        .lines()
        .map(|l| l.unwrap())
        .collect();
    writer.join().unwrap();
    assert!(child.wait().unwrap().success(), "{what} failed");
    assert_eq!(out.len(), n, "{what} answered too few lines");
    out
}

/// Run every program in a JavaScript engine (`tests/differential/engine.js`
/// under Node, or `INTY_NODE`), in one process. `None` when there is no
/// engine; on CI that fails the test instead.
pub fn run_engine(sources: &[String]) -> Option<Vec<Run>> {
    let node = std::env::var_os("INTY_NODE").unwrap_or_else(|| "node".into());
    if Command::new(&node).arg("--version").output().is_err() {
        assert!(
            std::env::var_os("CI").is_none(),
            "no JavaScript engine ({node:?}) on CI"
        );
        return None;
    }
    let script = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/differential/engine.js");
    let mut command = Command::new(node);
    command.arg(script);
    // One line per program: a program with anything but printable ASCII
    // (a line break, a line separator) goes as a JSON string after `JSON:`.
    let input: String = sources
        .iter()
        .map(|s| {
            if s.chars().any(|c| !(' '..='~').contains(&c)) {
                format!("JSON:{}\n", json_string(s))
            } else {
                s.clone() + "\n"
            }
        })
        .collect();
    Some(
        run_lines(command, "the JavaScript engine", input, sources.len())
            .iter()
            .map(|l| parse_run(l))
            .collect(),
    )
}

pub fn model_path() -> Option<PathBuf> {
    let path = match std::env::var_os("INTY_LEAN_MODEL") {
        Some(p) => PathBuf::from(p),
        None => {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean/.lake/build/bin/inty-model")
        }
    };
    path.exists().then_some(path)
}

/// A string as a JSON string literal.
pub fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ' '..='~' => out.push(c),
            c => {
                let mut units = [0u16; 2];
                for u in c.encode_utf16(&mut units) {
                    out.push_str(&format!("\\u{:04x}", u));
                }
            }
        }
    }
    out.push('"');
    out
}

/// A string's text in the wire format, as the model writes it
/// (`Inty.Wire.escape`): whitespace, parentheses and `%` as `%XX`.
pub fn escape(s: &str) -> String {
    s.chars()
        .map(|c| {
            if matches!(c, ' ' | '\t' | '\r' | '\n' | '(' | ')' | '%') {
                format!("%{:02X}", c as u32)
            } else {
                c.to_string()
            }
        })
        .collect()
}
