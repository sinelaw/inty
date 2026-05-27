//! Built-in (language-provided) Python module stubs.
//!
//! These are the modules inty ships with — `typing` and a curated slice
//! of the standard library — so common imports resolve without the user
//! supplying typeshed on the search path. Each is a plain `.pyi` file
//! under `stubs/`, read through the same [`super::pyi`] reader as any
//! external stub; this module is *only* the name → source registry, with
//! no stub content or resolver logic of its own.
//!
//! Adding a module is a one-line registry entry plus its `.pyi` file. The
//! import resolver consults this before the filesystem (see
//! `super::modules`), so a built-in shadows a same-named local file —
//! matching how the standard library shadows a stray `typing.py`.

/// The baked-in `.pyi` source for built-in module `spec`, if any.
pub fn builtin_module(spec: &str) -> Option<&'static str> {
    Some(match spec {
        "typing" => include_str!("stubs/typing.pyi"),
        "sys" => include_str!("stubs/sys.pyi"),
        "os" => include_str!("stubs/os.pyi"),
        "json" => include_str!("stubs/json.pyi"),
        "re" => include_str!("stubs/re.pyi"),
        "subprocess" => include_str!("stubs/subprocess.pyi"),
        "pathlib" => include_str!("stubs/pathlib.pyi"),
        "argparse" => include_str!("stubs/argparse.pyi"),
        _ => return None,
    })
}
