//! Built-in Python typeclass instance declarations.
//!
//! Declarative table of "type X implements class C in Python" for the
//! curated stdlib stubs. Each entry says: when a class `class` from
//! module `module` has been registered (its brand id allocated by the
//! pyi reader), install an instance for the named class into the
//! `InferState`'s class env.
//!
//! Built-in stdlib instances live here rather than as queryable class
//! members (dunders in the `.pyi` body) so the type-checker dispatches
//! through one mechanism — the per-language class env — not two.

use crate::ast::SourceLanguage;
use crate::infer::{Instance, InstanceBody, InstanceHead, InferState};
use crate::types::{ClassName, Type, TypeId};

/// One built-in instance declaration. `build` receives the class's
/// allocated brand id so the instance can refer to the class itself
/// (e.g. `Path.__truediv__ -> Path`).
struct BuiltinInstance {
    module: &'static str,
    class: &'static str,
    class_name: ClassName,
    build: fn(TypeId) -> Instance,
}

/// The full table. Add an entry per (module, class, class-name) triple.
const PYTHON_BUILTIN_INSTANCES: &[BuiltinInstance] = &[BuiltinInstance {
    module: "pathlib",
    class: "Path",
    class_name: ClassName::Div,
    build: build_path_div,
}];

fn build_path_div(id: TypeId) -> Instance {
    Instance {
        head: InstanceHead::Nominal(id),
        body: InstanceBody::Method {
            param: Type::String,
            ret: Type::Named(id, Vec::new()),
        },
    }
}

/// Install every built-in instance whose class has been registered in
/// the given `module`. Called by the stub loader right after a
/// built-in module's stub is read — at that point the pyi reader has
/// populated `state.class_brand_ids` with the module's class names.
pub fn install_for_module(state: &mut InferState, module: &str) {
    for entry in PYTHON_BUILTIN_INSTANCES {
        if entry.module != module {
            continue;
        }
        let Some(&id) = state.class_brand_ids.get(entry.class) else {
            continue;
        };
        let instance = (entry.build)(id);
        state.register_class_instance(SourceLanguage::Python, entry.class_name, instance);
    }
}
