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
    let dir = std::env::temp_dir().join(format!("inty_pyimports_{}_{}", std::process::id(), n));
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
    let env = resolve_python_imports(
        &mut state,
        env,
        &program,
        base_dir,
        search_paths,
        &mut visiting,
    )
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
    let ok1 = check(
        "from coll import items\nr = items(3)\nr\n",
        &dir,
        &[stubs.clone()],
    );
    assert_eq!(ok1.expect("omitting optional arg is fine"), "Number[]");
    let ok2 = check(
        "from coll import items\nr = items(3, 1)\nr\n",
        &dir,
        &[stubs],
    );
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
    write(
        &stubs,
        "mathx.pyi",
        "def add(a: int, b: int) -> int: ...\nPI: float\n",
    );
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
    let ty = check(
        "from dyn import passthru\nr = passthru(1) + 1\nr\n",
        &dir,
        &[stubs],
    );
    assert!(
        ty.is_ok(),
        "opaque export should not break the importer: {:?}",
        ty
    );
}

#[test]
fn pyi_optional_maps_to_union_with_null() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "opt.pyi",
        "def find(k: str) -> Optional[int]: ...\n",
    );
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
    assert!(
        ty.contains("Map") || ty.contains("Number"),
        "dict[str,int] -> Map<Number>, got {}",
        ty
    );
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
    let bad = check(
        "from geo import Point\np = Point(\"a\", 2)\n",
        &dir,
        &[stubs],
    );
    assert!(bad.is_err(), "stub constructor arg types must be enforced");
}

#[test]
fn pyi_stub_class_is_nominally_branded() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "geo.pyi",
        "class Point:\n    def __init__(self, x: int, y: int) -> None: ...\n    def dist(self) -> float: ...\n",
    );
    // A constructed instance carries the nominal brand: it prints as the
    // class name, not as its structural representation row.
    let ty = check(
        "from geo import Point\np = Point(1, 2)\np\n",
        &dir,
        &[stubs],
    )
    .expect("stub class construction");
    assert_eq!(ty, "Point");
}

#[test]
fn pyi_distinct_stub_classes_do_not_interchange() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // Two stub classes of identical (empty) shape. Before nominal
    // branding both mapped to the same structural row `{}` and collapsed
    // into one element type; now each has a distinct identity, so a list
    // holding both infers the *union* `A | B` rather than a single type.
    write(
        &stubs,
        "twins.pyi",
        "class A:\n    def __init__(self) -> None: ...\nclass B:\n    def __init__(self) -> None: ...\n",
    );
    let ty = check(
        "from twins import A, B\nxs = [A(), B()]\nxs\n",
        &dir,
        &[stubs],
    )
    .expect("two same-shape stub classes coexist in a list as a union");
    assert_eq!(ty, "(A | B)[]");
}

#[test]
fn pyi_generic_stub_class_ties_its_type_param() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // A generic container: the `TypeVar` T relates the constructor
    // argument to the method return, so `Box(5).get()` is a Number.
    write(
        &stubs,
        "box.pyi",
        "from typing import TypeVar, Generic\n\
         T = TypeVar(\"T\")\n\
         class Box(Generic[T]):\n\
         \x20   def __init__(self, value: T) -> None: ...\n\
         \x20   def get(self) -> T: ...\n",
    );
    let ty = check(
        "from box import Box\nb = Box(5)\nr = b.get() + 1\nr\n",
        &dir,
        &[stubs.clone()],
    )
    .expect("generic stub class should tie T across ctor and method");
    assert_eq!(ty, "Number");

    // The same class instantiated at String: get() yields a String, so
    // using it as a Number is a type error — proof T is tracked, not
    // collapsed to an unconstrained variable per occurrence.
    let bad = check(
        "from box import Box\nb = Box(\"x\")\nr = b.get() + 1\n",
        &dir,
        &[stubs],
    );
    assert!(
        bad.is_err(),
        "String-instantiated Box.get() must not be usable as a Number, got: {:?}",
        bad
    );
}

/// Stub with two distinct-shape classes, where `bark` is Dog-only and
/// `meow` is Cat-only. `x` is built as a `Dog | Cat` union.
fn pets_stub_and_union(stubs: &Path) -> String {
    write(
        stubs,
        "pets.pyi",
        "class Dog:\n\
         \x20   def __init__(self) -> None: ...\n\
         \x20   def bark(self) -> int: ...\n\
         class Cat:\n\
         \x20   def __init__(self) -> None: ...\n\
         \x20   def meow(self) -> int: ...\n",
    );
    "from pets import Dog, Cat\nx = Dog() if True else Cat()\n".to_string()
}

#[test]
fn isinstance_narrows_imported_stub_brand() {
    // isinstance narrowing works on imported .pyi class brands, not just
    // source classes: `class_brand_ids` is populated for stub classes.
    let dir = tmp_dir();
    let stubs = tmp_dir();
    let prelude = pets_stub_and_union(&stubs);

    // Control: the bare union has no Dog-only member.
    let bad = check(&format!("{prelude}r = x.bark()\n"), &dir, &[stubs.clone()]);
    assert!(
        bad.is_err(),
        "x.bark() on a Dog | Cat union should fail without narrowing"
    );

    // isinstance narrows x to Dog in the true branch.
    let ok = check(
        &format!("{prelude}if isinstance(x, Dog):\n    r = x.bark()\n"),
        &dir,
        &[stubs.clone()],
    );
    assert!(
        ok.is_ok(),
        "isinstance(x, Dog) should narrow imported x to Dog, got {:?}",
        ok
    );

    // Proof it's a real narrowing: the Cat-only method is still rejected.
    let still_bad = check(
        &format!("{prelude}if isinstance(x, Dog):\n    r = x.meow()\n"),
        &dir,
        &[stubs],
    );
    assert!(
        still_bad.is_err(),
        "x.meow() inside the Dog branch should be rejected"
    );
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
    assert!(
        ty.is_ok(),
        "overloaded def should be opaque, not error: {:?}",
        ty
    );
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
    write(
        &stubs,
        "impl.pyi",
        "def helper(x: int) -> int: ...\nINTERNAL: int\n",
    );
    write(&stubs, "agg.pyi", "from impl import helper as helper\n");
    // `helper` is re-exported; `INTERNAL` is not.
    assert!(check(
        "from agg import helper\nr = helper(3)\nr\n",
        &dir,
        &[stubs.clone()]
    )
    .is_ok());
    assert!(
        check("from agg import INTERNAL\n", &dir, &[stubs]).is_err(),
        "a name not named in the re-export must not be visible"
    );
}

#[test]
fn pyi_literal_maps_to_literal_union() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "lit.pyi",
        "def kind() -> Literal[\"a\", \"b\"]: ...\n",
    );
    let ty = check("from lit import kind\nkind()\n", &dir, &[stubs]).expect("literal return");
    // Should be the literal union "a" | "b", not opaque.
    assert!(
        ty.contains("\"a\"") && ty.contains("\"b\""),
        "Literal[\"a\", \"b\"] should map to a literal union, got {}",
        ty
    );
}

#[test]
fn pyi_literal_param_is_enforced() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "lit.pyi",
        "def pick(x: Literal[\"a\", \"b\"]) -> int: ...\n",
    );
    assert!(
        check(
            "from lit import pick\npick(\"a\")\n",
            &dir,
            &[stubs.clone()]
        )
        .is_ok(),
        "a valid literal member should be accepted"
    );
    assert!(
        check("from lit import pick\npick(\"c\")\n", &dir, &[stubs]).is_err(),
        "a value outside the literal union must be rejected"
    );
}

#[test]
fn pyi_callable_maps_to_function_type() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "hof.pyi",
        "def apply(f: Callable[[int], int], x: int) -> int: ...\n",
    );
    // A matching 1-arg callback type-checks; the result is the return type.
    let ty = check(
        "from hof import apply\ndef g(n):\n    return n + 1\nr = apply(g, 1)\nr\n",
        &dir,
        &[stubs.clone()],
    )
    .expect("matching callback should type-check");
    assert_eq!(ty, "Number");

    // A wrong-arity callback is rejected — Callable shape is enforced.
    assert!(
        check(
            "from hof import apply\ndef g(a, b):\n    return a\nr = apply(g, 1)\n",
            &dir,
            &[stubs],
        )
        .is_err(),
        "a 2-arg callback must not satisfy Callable[[int], int]"
    );
}

#[test]
fn pyi_callable_ellipsis_is_opaque() {
    let dir = tmp_dir();
    let stubs = tmp_dir();
    // `Callable[..., int]` (arbitrary args) can't be expressed; stays
    // opaque so any call shape is accepted.
    write(
        &stubs,
        "hof2.pyi",
        "def deco(f: Callable[..., int]) -> int: ...\n",
    );
    let ty = check(
        "from hof2 import deco\ndef g(a, b, c):\n    return 1\nr = deco(g)\nr\n",
        &dir,
        &[stubs],
    );
    assert!(
        ty.is_ok(),
        "Callable[..., R] should accept any callable: {:?}",
        ty
    );
}

#[test]
fn transitive_py_imports() {
    let dir = tmp_dir();
    write(&dir, "a.py", "def base(x):\n    return x + 1\n");
    write(
        &dir,
        "b.py",
        "from a import base\ndef twice(x):\n    return base(base(x))\n",
    );
    let ty = check("from b import twice\nr = twice(10)\nr\n", &dir, &[]).expect("transitive");
    assert_eq!(ty, "Number");
}

#[test]
fn imported_class_resolves_as_type_annotation() {
    // A class imported from a stub resolves as a type annotation — both
    // the bare form (`Dog`) and the dotted/qualified form (`animals.Dog`)
    // bring in the real class brand, not an opaque variable.
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(
        &stubs,
        "animals.pyi",
        "class Dog:\n    def __init__(self) -> None: ...\n",
    );

    // Correct usage type-checks.
    let ok = check(
        "import animals\nfrom animals import Dog\n\
         def f(d: animals.Dog):\n    return 1\n\
         def g(d: Dog):\n    return 1\n\
         f(Dog())\ng(Dog())\n",
        &dir,
        &[stubs.clone()],
    );
    assert!(
        ok.is_ok(),
        "imported class annotations should check: {:?}",
        ok
    );

    // A non-Dog argument is rejected — the dotted annotation resolved to
    // the real brand, not opaque.
    let bad = check(
        "import animals\ndef f(d: animals.Dog):\n    return 1\nf(\"nope\")\n",
        &dir,
        &[stubs],
    );
    assert!(
        bad.is_err(),
        "String where animals.Dog is annotated should fail"
    );
}

#[test]
fn typing_module_is_built_in() {
    // `typing` resolves with no stub files on the search path — it's a
    // built-in module. Its constructors work as types (bare and
    // qualified) and still enforce element types.
    let dir = tmp_dir();
    let ok = check(
        "from typing import List, Optional\n\
         def f(xs: List[int]) -> Optional[int]:\n    return None\n\
         f([1, 2])\n",
        &dir,
        &[],
    );
    assert!(ok.is_ok(), "typing imports should resolve: {:?}", ok);

    let ok2 = check(
        "import typing\ndef g(xs: typing.List[int]):\n    return xs[0] + 1\ng([1])\n",
        &dir,
        &[],
    );
    assert!(
        ok2.is_ok(),
        "qualified typing.List should resolve: {:?}",
        ok2
    );

    let bad = check(
        "from typing import List\ndef h(xs: List[int]):\n    return xs[0]\nr = h([1]) + \"s\"\n",
        &dir,
        &[],
    );
    assert!(bad.is_err(), "List[int] element type should be enforced");
}

#[test]
fn stdlib_modules_are_built_in() {
    // A curated slice of the standard library resolves from baked-in
    // stubs with no files on the search path, and the stub classes'
    // members are typed (a wrong member is caught).
    let dir = tmp_dir();
    let ok = check(
        "import sys\nimport json\nimport subprocess\nimport re\n\
         s = json.dumps([1, 2])\n\
         args = sys.argv\n\
         r = subprocess.run([\"ls\"])\n\
         rc = r.returncode\n\
         pat = re.compile(\"x\")\n\
         hits = pat.findall(\"xx\")\n",
        &dir,
        &[],
    );
    assert!(ok.is_ok(), "stdlib imports should resolve: {:?}", ok);

    let bad = check(
        "import subprocess\nr = subprocess.run([\"ls\"])\nx = r.nonexistent\n",
        &dir,
        &[],
    );
    assert!(
        bad.is_err(),
        "an absent member of a stub class should be caught"
    );
}

#[test]
fn module_level_stub_class_instance_accessed_from_function() {
    // Issue #71: a module-level binding of a stub class instance,
    // accessed via method or field from inside a function body, hits
    // the hoisted-unify path with an open-tailed row constraint meeting
    // the brand. Before the nominal-vs-open-row unroll rule in
    // `unify`, this rejected with a "row vs Path" mismatch. The
    // canonical pathlib pattern from real scripts is the regression
    // case.
    let dir = tmp_dir();
    let src = "from pathlib import Path

ROOT = Path('Cargo.toml')

def f() -> str:
    return ROOT.read_text()
";
    check(src, &dir, &[]).expect("module-level Path read from a function must type-check");

    // Also exercise the keyword-argument path through a Pattern method
    // (`re.compile(...).subn(repl, s, count=1)`), which originally
    // surfaced the same bug a second time in `bump-version.py`.
    let src2 = "import re

PAT = re.compile(r'x', re.DOTALL)

def f(s: str) -> str:
    new_s, _count = PAT.subn('y', s, count=1)
    return new_s
";
    check(src2, &dir, &[]).expect("module-level Pattern + subn keyword call must type-check");
}

#[test]
fn keyword_arguments_through_stub_signature() {
    // Parameter names from a `.pyi` signature drive keyword resolution
    // at the call site.
    let dir = tmp_dir();
    let stubs = tmp_dir();
    write(&stubs, "geo.pyi", "def dist(x: int, y: int) -> int: ...\n");
    let ok = check(
        "from geo import dist\nr = dist(y=2, x=1)\nr\n",
        &dir,
        &[stubs.clone()],
    );
    assert_eq!(ok.expect("keyword call via stub names"), "Number");

    let bad = check("from geo import dist\nr = dist(1, z=2)\n", &dir, &[stubs]);
    assert!(
        bad.is_err(),
        "unknown keyword against a stub signature should fail"
    );
}
