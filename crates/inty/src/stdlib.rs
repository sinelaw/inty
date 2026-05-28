//! Embedded standard library declaration files.
//!
//! Each `.d.js` file is baked into the binary at compile time with
//! `include_str!` and loaded into the initial type environment before user
//! code is checked. The files are regular inty-checkable JavaScript
//! declarations — the same format any user can write — but they're never
//! executed, so they use `const name;` (no initializer) to declare external
//! bindings.

use crate::builtins::initial_env;
use crate::error::IntyError;
use crate::frontends::javascript::parse;
use crate::infer::{InferState, TypeEnv};

/// Core built-ins: console, Math, parseInt, parseFloat, isNaN, isFinite.
pub const CORE: &str = include_str!("../stdlib/core.d.js");

/// Browser DOM: document, window, setTimeout, alert.
pub const DOM: &str = include_str!("../stdlib/dom.d.js");

/// Default stdlib libraries loaded by the CLI before user code.
///
/// Each entry is `(source, name-for-errors)`. Order matters: later libs
/// can reference names from earlier ones.
pub const DEFAULT_LIBS: &[(&str, &str)] =
    &[(CORE, "<stdlib/core.d.js>"), (DOM, "<stdlib/dom.d.js>")];

/// Load a single declaration file into the given environment.
///
/// Parses `source`, runs inference, and returns the resulting environment.
/// The `InferState` is threaded through so that type variable IDs stay
/// unique across the lib and the subsequent user program.
pub fn load_lib(state: &mut InferState, env: TypeEnv, source: &str) -> Result<TypeEnv, IntyError> {
    let program = parse(source)?;
    let (_ty, new_env) = state.infer_program_with_env(&env, &program)?;
    Ok(new_env)
}

/// Build the initial environment with all default stdlib libs loaded.
///
/// Returns the environment plus the fresh `InferState` used to load the
/// libs. Callers should continue inferring their user program with the
/// returned state so type variable IDs remain unique.
pub fn initial_env_with_stdlib() -> Result<(TypeEnv, InferState), IntyError> {
    let mut state = InferState::new();
    let mut env = initial_env();
    for (source, _name) in DEFAULT_LIBS {
        env = load_lib(&mut state, env, source)?;
    }
    Ok((env, state))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_lib_parses_and_checks() {
        let mut state = InferState::new();
        let env = initial_env();
        let result = load_lib(&mut state, env, CORE);
        assert!(result.is_ok(), "core.d.js failed: {:?}", result.err());
    }

    #[test]
    fn dom_lib_parses_and_checks() {
        let mut state = InferState::new();
        let env = initial_env();
        let result = load_lib(&mut state, env, DOM);
        assert!(result.is_ok(), "dom.d.js failed: {:?}", result.err());
    }

    #[test]
    fn stdlib_binds_console_and_math() {
        let (env, _state) = initial_env_with_stdlib().unwrap();
        assert!(env.lookup("console").is_some());
        assert!(env.lookup("Math").is_some());
        assert!(env.lookup("parseInt").is_some());
    }

    #[test]
    fn stdlib_binds_document_and_window() {
        let (env, _state) = initial_env_with_stdlib().unwrap();
        assert!(env.lookup("document").is_some());
        assert!(env.lookup("window").is_some());
        assert!(env.lookup("setTimeout").is_some());
    }

    /// The `Element<T>` alias added to `dom.d.js` should be usable from
    /// user code as a function-parameter annotation. Pins the typical
    /// htmx-class pattern: a helper takes a DOM element parameter and
    /// chains methods on it. Before the alias, users had to inline the
    /// ~70-field row at every annotation site; with it, `Element<a>`
    /// suffices.
    #[test]
    fn element_alias_is_usable_in_function_annotations() {
        use crate::frontends::javascript::parse;
        let (env, mut state) = initial_env_with_stdlib().unwrap();
        let src = "\
            /** function hasFooClass<T>(elt: Element<T>) => Boolean */ \
            function hasFooClass(elt) { return elt.classList.contains(\"foo\"); } \
            /** function elementId<T>(elt: Element<T>) => String */ \
            function elementId(elt) { return elt.id; }";
        let mut program = parse(src).expect("source must parse");
        // The dom.d.js stdlib already registered the `Element<T>` alias
        // on `state.type_aliases` during `initial_env_with_stdlib`; the
        // user-program parse doesn't introduce additional aliases.
        program.type_aliases = Vec::new();
        let result = state.infer_program_with_env(&env, &program);
        assert!(
            result.is_ok(),
            "Element<T> alias should accept method chaining, got: {:?}",
            result.err()
        );
    }

    /// `Node<T>` for the smaller (non-Element) node case. Used for
    /// document fragments, text nodes, etc.
    #[test]
    fn node_alias_is_usable_in_function_annotations() {
        use crate::frontends::javascript::parse;
        let (env, mut state) = initial_env_with_stdlib().unwrap();
        let src = "\
            /** function nodeName<T>(n: Node<T>) => String */ \
            function nodeName(n) { return n.nodeName; }";
        let mut program = parse(src).expect("source must parse");
        program.type_aliases = Vec::new();
        let result = state.infer_program_with_env(&env, &program);
        assert!(
            result.is_ok(),
            "Node<T> alias should accept .nodeName, got: {:?}",
            result.err()
        );
    }
}
