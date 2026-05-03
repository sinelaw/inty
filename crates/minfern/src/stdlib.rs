//! Embedded standard library declaration files.
//!
//! Each `.d.js` file is baked into the binary at compile time with
//! `include_str!` and loaded into the initial type environment before user
//! code is checked. The files are regular minfern-checkable JavaScript
//! declarations — the same format any user can write — but they're never
//! executed, so they use `const name;` (no initializer) to declare external
//! bindings.

use crate::builtins::initial_env;
use crate::error::MinfernError;
use crate::infer::{InferState, TypeEnv};
use crate::parser::parse;

/// Core built-ins: console, Math, parseInt, parseFloat, isNaN, isFinite.
pub const CORE: &str = include_str!("../stdlib/core.d.js");

/// Browser DOM: document, window, setTimeout, alert.
pub const DOM: &str = include_str!("../stdlib/dom.d.js");

/// Default stdlib libraries loaded by the CLI before user code.
///
/// Each entry is `(source, name-for-errors)`. Order matters: later libs
/// can reference names from earlier ones.
pub const DEFAULT_LIBS: &[(&str, &str)] = &[(CORE, "<stdlib/core.d.js>"), (DOM, "<stdlib/dom.d.js>")];

/// Load a single declaration file into the given environment.
///
/// Parses `source`, runs inference, and returns the resulting environment.
/// The `InferState` is threaded through so that type variable IDs stay
/// unique across the lib and the subsequent user program.
pub fn load_lib(
    state: &mut InferState,
    env: TypeEnv,
    source: &str,
) -> Result<TypeEnv, MinfernError> {
    let program = parse(source)?;
    let (_ty, new_env) = state.infer_program_with_env(&env, &program)?;
    Ok(new_env)
}

/// Build the initial environment with all default stdlib libs loaded.
///
/// Returns the environment plus the fresh `InferState` used to load the
/// libs. Callers should continue inferring their user program with the
/// returned state so type variable IDs remain unique.
pub fn initial_env_with_stdlib() -> Result<(TypeEnv, InferState), MinfernError> {
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
}
