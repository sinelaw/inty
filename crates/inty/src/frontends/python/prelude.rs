//! The Python builtin prelude: a curated `builtins.pyi` providing the
//! builtin value namespace (`print`, `len`, `range`, …) that every Python
//! program implicitly imports. Loaded through the same `.pyi` reader used
//! for stub imports, so its signatures lower via `type_expr`. See #55 and
//! `builtins.pyi` for the modelling rationale.

use crate::error::Result;
use crate::infer::{InferState, TypeEnv};

use super::pyi::read_stub;

/// The curated builtins stub, baked into the binary.
pub const PRELUDE: &str = include_str!("builtins.pyi");

/// Extend `env` with the Python builtin namespace. Fresh type-variable
/// ids are drawn from `state` so they don't clash with the user program.
pub fn load(state: &mut InferState, mut env: TypeEnv) -> Result<TypeEnv> {
    let module = read_stub(state, PRELUDE)?;
    for (name, scheme) in module.exports {
        env = env.extend(name, scheme);
    }
    Ok(env)
}
