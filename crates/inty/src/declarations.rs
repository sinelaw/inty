//! Emit `.d.js` declarations from a checked module.
//!
//! Walks a module's effective export table (produced by `crate::modules`)
//! and renders each export as a stdlib-style line:
//!
//! ```text
//! /** const NAME: T */
//! const NAME;
//! ```
//!
//! This is the public-surface artefact downstream tools consume — for
//! example, `fresh` uses it to publish each plugin's exported types so
//! other plugins can `import` against them. Internal (non-exported)
//! bindings are not emitted.
//!
//! # Public API
//!
//! ```ignore
//! pub fn emit_declarations(module: &CheckedModule) -> String;
//! ```
//!
//! `CheckedModule` bundles the inferred environment and the export
//! table for one source file, in the same shape `modules::load_module`
//! returns internally.

use crate::infer::TypeEnv;
use crate::modules::{ExportBinding, ExportEntry, ExportTable};
use crate::types::{PrettyContext, TypeScheme};

/// A fully type-checked module, ready for declaration emission.
///
/// Carries the inferred environment alongside the effective export
/// table (with `export … from` re-exports already resolved to inline
/// schemes). Shape matches what `crate::modules::load_module` produces
/// internally.
#[derive(Debug, Clone)]
pub struct CheckedModule {
    pub env: TypeEnv,
    pub exports: ExportTable,
}

impl CheckedModule {
    pub fn new(env: TypeEnv, exports: ExportTable) -> Self {
        CheckedModule { env, exports }
    }
}

/// Output flavor for [`emit_declarations`]. The default `Inty`
/// flavor matches `stdlib/*.d.js`; the `Ts` flavor produces TS
/// `declare const NAME: T;` lines suitable for a `.d.ts` consumer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationFlavor {
    Inty,
    Ts,
}

impl Default for DeclarationFlavor {
    fn default() -> Self {
        DeclarationFlavor::Inty
    }
}

/// Emit `.d.js` declarations for a checked module's exports.
///
/// Each export becomes a `/** const NAME: T */ const NAME;` pair.
/// Internal bindings are omitted. Output ends with a trailing newline.
///
/// Predicates on a scheme (e.g. `Plus a`) are dropped from the emitted
/// type — the existing stdlib annotation form has no surface for `where`
/// clauses and consumers rely on the body only. Polymorphic exports are
/// emitted with type variables in scope; the type parser auto-quantifies
/// at the binding level on re-import, matching how `stdlib/core.d.js`
/// declarations work.
pub fn emit_declarations(module: &CheckedModule) -> String {
    emit_declarations_with_flavor(module, DeclarationFlavor::Inty)
}

/// Emit declarations in the requested flavor. With
/// `DeclarationFlavor::Ts`, output uses TypeScript syntax — one
/// `declare const NAME: T;` line per export, suitable for a `.d.ts`
/// file other TS tooling can consume.
pub fn emit_declarations_with_flavor(module: &CheckedModule, flavor: DeclarationFlavor) -> String {
    let mut out = String::new();
    for entry in &module.exports {
        if let Some(scheme) = resolve_scheme(entry, &module.env) {
            match flavor {
                DeclarationFlavor::Inty => emit_one(&mut out, &entry.exported, &scheme),
                DeclarationFlavor::Ts => emit_one_ts(&mut out, &entry.exported, &scheme),
            }
        }
    }
    out
}

fn resolve_scheme(entry: &ExportEntry, env: &TypeEnv) -> Option<TypeScheme> {
    match &entry.binding {
        ExportBinding::Local(name) => env.lookup(name).cloned(),
        ExportBinding::Inline(s) => Some(s.clone()),
    }
}

fn emit_one(out: &mut String, name: &str, scheme: &TypeScheme) {
    let mut ctx = PrettyContext::new();
    let body = ctx.format_type(&scheme.body.ty);
    out.push_str("/** const ");
    out.push_str(name);
    out.push_str(": ");
    out.push_str(&body);
    out.push_str(" */\n");
    out.push_str("const ");
    out.push_str(name);
    out.push_str(";\n");
}

fn emit_one_ts(out: &mut String, name: &str, scheme: &TypeScheme) {
    let mut ctx = PrettyContext::new();
    let body = ctx.format_type_ts(&scheme.body.ty);
    out.push_str("declare const ");
    out.push_str(name);
    out.push_str(": ");
    out.push_str(&body);
    out.push_str(";\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modules::ExportEntry;
    use crate::types::Type;

    fn make_env_with(name: &str, ty: Type) -> TypeEnv {
        TypeEnv::empty().extend(name.to_string(), TypeScheme::mono(ty))
    }

    #[test]
    fn emit_const_number() {
        let env = make_env_with("answer", Type::Number);
        let exports = vec![ExportEntry {
            exported: "answer".to_string(),
            binding: ExportBinding::Local("answer".to_string()),
        }];
        let module = CheckedModule::new(env, exports);
        let out = emit_declarations(&module);
        assert_eq!(out, "/** const answer: Number */\nconst answer;\n");
    }

    #[test]
    fn emit_function() {
        let env = make_env_with("id", Type::simple_func(vec![Type::String], Type::String));
        let exports = vec![ExportEntry {
            exported: "id".to_string(),
            binding: ExportBinding::Local("id".to_string()),
        }];
        let module = CheckedModule::new(env, exports);
        let out = emit_declarations(&module);
        assert_eq!(out, "/** const id: (String) => String */\nconst id;\n");
    }

    #[test]
    fn skips_internal_bindings() {
        let env = TypeEnv::empty()
            .extend("exported".to_string(), TypeScheme::mono(Type::Boolean))
            .extend("internal".to_string(), TypeScheme::mono(Type::Number));
        let exports = vec![ExportEntry {
            exported: "exported".to_string(),
            binding: ExportBinding::Local("exported".to_string()),
        }];
        let module = CheckedModule::new(env, exports);
        let out = emit_declarations(&module);
        assert!(out.contains("exported"));
        assert!(!out.contains("internal"));
    }

    #[test]
    fn ts_flavor_emits_declare_const_lines() {
        // TS-flavor output uses `declare const NAME: T;` with
        // lowercase TS primitives and `;`-separated object types.
        let env = TypeEnv::empty()
            .extend("answer".to_string(), TypeScheme::mono(Type::Number))
            .extend(
                "cfg".to_string(),
                TypeScheme::mono(Type::object([
                    ("name", Type::String),
                    ("count", Type::Number),
                ])),
            );
        let exports = vec![
            ExportEntry {
                exported: "answer".to_string(),
                binding: ExportBinding::Local("answer".to_string()),
            },
            ExportEntry {
                exported: "cfg".to_string(),
                binding: ExportBinding::Local("cfg".to_string()),
            },
        ];
        let module = CheckedModule::new(env, exports);
        let out = emit_declarations_with_flavor(&module, DeclarationFlavor::Ts);
        assert!(out.contains("declare const answer: number;"));
        assert!(out.contains("declare const cfg:"));
        // TS-flavor row should use semicolons between fields.
        assert!(out.contains("name: string"));
        assert!(out.contains("count: number"));
    }

    #[test]
    fn round_trip_through_load_lib() {
        use crate::infer::InferState;
        use crate::modules::check_module;
        use crate::stdlib::load_lib;
        use std::io::Write;

        // Hand-rolled temp dir to avoid adding a `tempfile` dev-dep —
        // matches the pattern in `modules::tests`.
        let base = std::env::temp_dir();
        let pid = std::process::id();
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let dir = base.join(format!("inty-decls-{}-{}", pid, nonce));
        std::fs::create_dir_all(&dir).unwrap();

        let entry = dir.join("entry.js");
        let mut f = std::fs::File::create(&entry).unwrap();
        f.write_all(
            b"export var answer = 42;\n\
              export function id(x) { return x; }\n\
              export function add(a, b) { return a + b; }\n\
              var hidden = 99;\n",
        )
        .unwrap();
        drop(f);

        let mut state = InferState::new();
        let env = crate::builtins::initial_env();
        let (module_env, exports) = check_module(&mut state, env.clone(), &entry).unwrap();
        let module = CheckedModule::new(module_env, exports);
        let emitted = emit_declarations(&module);

        let _ = std::fs::remove_dir_all(&dir);

        assert!(emitted.contains("answer"));
        assert!(emitted.contains("id"));
        assert!(emitted.contains("add"));
        assert!(!emitted.contains("hidden"));

        let mut state2 = InferState::new();
        let env2 = load_lib(&mut state2, env, &emitted).unwrap();

        assert!(env2.lookup("answer").is_some());
        assert!(env2.lookup("id").is_some());
        assert!(env2.lookup("add").is_some());
        assert!(env2.lookup("hidden").is_none());
    }

    #[test]
    fn inline_reexport_uses_stored_scheme() {
        let env = TypeEnv::empty();
        let exports = vec![ExportEntry {
            exported: "fromOther".to_string(),
            binding: ExportBinding::Inline(TypeScheme::mono(Type::String)),
        }];
        let module = CheckedModule::new(env, exports);
        let out = emit_declarations(&module);
        assert_eq!(out, "/** const fromOther: String */\nconst fromOther;\n");
    }
}
