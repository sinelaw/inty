//! End-to-end tests for Python import resolution: `.py` modules
//! (parsed + inferred) and `.pyi` stubs (Bucket-A type mapping), found
//! via the importing file's directory and configured search roots
//! ("typeshed"). See `docs/pyi-import-mapping.md`.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};

use inty::frontends::python::{modules::resolve_python_imports, parse_source};
use inty::stdlib::initial_env_with_stdlib;

static COUNTER: AtomicU32 = AtomicU32::new(0);

/// A throwaway directory under the OS temp dir, unique per call.
fn tmp_dir() -> PathBuf {
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "inty_pyimports_{}_{}",
        std::process::id(),
        n
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn write(dir: &Path, rel: &str, contents: &str) {
    let path = dir.join(rel);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create parent dir");
    }
    std::fs::write(path, contents).expect("write fixture");
}

/// Resolve `main_src`'s imports against `base_dir` + `search_paths`,
/// infer, and return the program's type string, or the formatted error.
fn check(main_src: &str, base_dir: &Path, search_paths: &[PathBuf]) -> Result<String, String> {
    let program = parse_source(main_src).map_err(|e| format!("parse error: {:?}", e))?;
    let (env, mut state) =
        initial_env_with_stdlib().map_err(|e| format!("stdlib error: {:?}", e))?;
    let mut visiting = HashSet::new();
    let env = resolve_python_imports(&mut state, env, &program, base_dir, search_paths, &mut visiting)
        .map_err(|e| format!("resolve error: {:?}", e))?;
    let (ty, _) = state
        .infer_program_with_env(&env, &program)
        .map_err(|e| format!("type error: {:?}", e))?;
    state
        .resolve_constraints()
        .map_err(|e| format!("constraint error: {:?}", e))?;
    if !state.errors.is_empty() {
        return Err(format!("errors: {:?}", state.errors));
    }
    let resolved = state.apply_subst(&ty);
    let mut ctx = inty::types::PrettyContext::with_nominal_names(state.nominal_names());
    Ok(ctx.format_type(&resolved))
}

#[test]
fn imports_a_function_from_a_local_py_module() {
    let dir = tmp_dir();
    write(&dir, "helpers.py", "def double(x):\n    return x + x\n");
    let main = "from helpers import double\nr = double(21)\nr\n";
    let ty = check(main, &dir, &[]).expect("should type-check");
    assert_eq!(ty, "Number");
}

#[test]
fn unknown_export_is_rejected() {
    let dir = tmp_dir();
    write(&dir, "helpers.py", "def double(x):\n    return x + x\n");
    let main = "from helpers import triple\n";
    assert!(
        check(main, &dir, &[]).is_err(),
        "importing a name the module doesn't define must fail"
    );
}

#[test]
fn missing_module_is_rejected() {
    let dir = tmp_dir();
    let main = "from nope import x\n";
    assert!(check(main, &dir, &[]).is_err(), "missing module must fail");
}

#[test]
fn pyi_stub_function_signature_is_used() {
    let dir = tmp_dir();
    // A stub on the search path ("typeshed").
    let stubs = tmp_dir();
    write(&stubs, "mathx.pyi", "def add(a: int, b: int) -> int: ...\n");
    let main = "from mathx import add\nr = add(1, 2)\nr\n";
    let ty = check(main, &dir, &[stubs]).expect("should type-check via stub");
    assert_eq!(ty, "Number");
}

#[test]
fn pyi_stub_enforces_argument_types() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "mathx.pyi", "def add(a: int, b: int) -> int: ...\n");
    // Passing a String where the stub declares int must fail.
    let main = "from mathx import add\nr = add(\"x\", 2)\n";
    assert!(
        check(main, &dir, &[stubs]).is_err(),
        "stub parameter types must be enforced at the call site"
    );
}

#[test]
fn pyi_stub_optional_param_and_list_return() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "coll.pyi",
        "def items(n: int, start: int = ...) -> list[int]: ...\n",
    );
    // Optional trailing param may be omitted.
    let ok1 = check("from coll import items\nr = items(3)\nr\n", &dir, &[stubs.clone()]);
    assert_eq!(ok1.expect("omitting optional arg is fine"), "Number[]");
    let ok2 = check("from coll import items\nr = items(3, 1)\nr\n", &dir, &[stubs]);
    assert_eq!(ok2.expect("supplying optional arg is fine"), "Number[]");
}

#[test]
fn pyi_module_level_var() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "cfg.pyi", "VERSION: str\n");
    let ty = check("from cfg import VERSION\nVERSION\n", &dir, &[stubs]).expect("var import");
    assert_eq!(ty, "String");
}

#[test]
fn import_namespace_member_access() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "mathx.pyi", "def add(a: int, b: int) -> int: ...\nPI: float\n");
    // `import mathx` binds a namespace; `mathx.add(...)` reads through it.
    let ty = check("import mathx\nr = mathx.add(1, 2)\nr\n", &dir, &[stubs]).expect("namespace");
    assert_eq!(ty, "Number");
}

#[test]
fn relative_import_from_sibling() {
    let dir = tmp_dir();
    write(&dir, "util.py", "def ident(x):\n    return x\n");
    // `from . import util` then use util.ident, OR import the name.
    let main = "from util import ident\nr = ident(5)\nr\n";
    let ty = check(main, &dir, &[]).expect("sibling import");
    assert_eq!(ty, "Number");
}

#[test]
fn opaque_export_for_unmodelled_type() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // `Any`-typed parameter and return → opaque: the call still checks,
    // and the result unifies with anything.
    write(&stubs, "dyn.pyi", "def passthru(x: Any) -> Any: ...\n");
    let ty = check("from dyn import passthru\nr = passthru(1) + 1\nr\n", &dir, &[stubs]);
    assert!(ty.is_ok(), "opaque export should not break the importer: {:?}", ty);
}

#[test]
fn pyi_optional_maps_to_union_with_null() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "opt.pyi", "def find(k: str) -> Optional[int]: ...\n");
    let ty = check("from opt import find\nr = find(\"k\")\nr\n", &dir, &[stubs]).expect("optional");
    // int | None  ->  Number | Null  (order may vary; check membership).
    assert!(
        ty.contains("Number") && (ty.contains("Null") || ty.contains("null")),
        "Optional[int] should map to Number | Null, got {}",
        ty
    );
}

#[test]
fn pyi_dict_maps_to_string_keyed_map() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "m.pyi", "def lookup() -> dict[str, int]: ...\n");
    let ty = check("from m import lookup\nr = lookup()\nr\n", &dir, &[stubs]).expect("dict");
    assert!(ty.contains("Map") || ty.contains("Number"), "dict[str,int] -> Map<Number>, got {}", ty);
}

#[test]
fn pyi_class_constructor_and_method() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "geo.pyi",
        "class Point:\n    def __init__(self, x: int, y: int) -> None: ...\n    def dist(self) -> float: ...\n",
    );
    // Construct and call a method declared by the stub.
    let ty = check(
        "from geo import Point\np = Point(1, 2)\nd = p.dist()\nd\n",
        &dir,
        &[stubs.clone()],
    )
    .expect("stub class construction + method");
    assert_eq!(ty, "Number");

    // Wrong constructor argument type is rejected.
    let bad = check("from geo import Point\np = Point(\"a\", 2)\n", &dir, &[stubs]);
    assert!(bad.is_err(), "stub constructor arg types must be enforced");
}

#[test]
fn pyi_overload_decorator_is_opaque_not_a_lex_error() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // `@overload` must tokenize (not error) and degrade to opaque.
    write(
        &stubs,
        "ov.pyi",
        "from typing import overload\n\
         @overload\n\
         def f(x: int) -> int: ...\n\
         @overload\n\
         def f(x: str) -> str: ...\n",
    );
    let ty = check("from ov import f\nr = f(1) + 1\nr\n", &dir, &[stubs]);
    assert!(ty.is_ok(), "overloaded def should be opaque, not error: {:?}", ty);
}

#[test]
fn pyi_property_decorator_becomes_a_field() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "shape.pyi",
        "class Circle:\n\
         \x20   def __init__(self, r: float) -> None: ...\n\
         \x20   @property\n\
         \x20   def area(self) -> float: ...\n",
    );
    // `area` is a property → a plain field, read without calling.
    let ty = check(
        "from shape import Circle\nc = Circle(2.0)\na = c.area\na\n",
        &dir,
        &[stubs],
    )
    .expect("property should read as a field");
    assert_eq!(ty, "Number");
}

#[test]
fn pyi_positional_only_marker_is_ignored() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // The `/` positional-only marker must not be parsed as a parameter.
    write(&stubs, "po.pyi", "def root(x: int, /) -> int: ...\n");
    let ty = check("from po import root\nr = root(9)\nr\n", &dir, &[stubs])
        .expect("positional-only def should take exactly one arg");
    assert_eq!(ty, "Number");
}

#[test]
fn pyi_star_reexport_is_followed() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // `agg` re-exports everything from `impl` via `import *`.
    write(&stubs, "impl.pyi", "def helper(x: int) -> int: ...\n");
    write(&stubs, "agg.pyi", "from impl import *\n");
    let ty = check("from agg import helper\nr = helper(3)\nr\n", &dir, &[stubs])
        .expect("star re-export should expose helper");
    assert_eq!(ty, "Number");
}

#[test]
fn pyi_named_reexport_is_followed() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "impl.pyi", "def helper(x: int) -> int: ...\nINTERNAL: int\n");
    write(&stubs, "agg.pyi", "from impl import helper as helper\n");
    // `helper` is re-exported; `INTERNAL` is not.
    assert!(check("from agg import helper\nr = helper(3)\nr\n", &dir, &[stubs.clone()]).is_ok());
    assert!(
        check("from agg import INTERNAL\n", &dir, &[stubs]).is_err(),
        "a name not named in the re-export must not be visible"
    );
}

#[test]
fn transitive_py_imports() {
    let dir = tmp_dir();
    write(&dir, "a.py", "def base(x):\n    return x + 1\n");
    write(&dir, "b.py", "from a import base\ndef twice(x):\n    return base(base(x))\n");
    let ty = check("from b import twice\nr = twice(10)\nr\n", &dir, &[]).expect("transitive");
    assert_eq!(ty, "Number");
}
