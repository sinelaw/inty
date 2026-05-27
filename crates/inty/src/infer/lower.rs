//! Lowering of the frontend-neutral [`TypeAst`] IR into a concrete
//! [`Type`].
//!
//! This is the single semantic home for turning a parsed type expression
//! into an inty type: it mints fresh variables for [`TypeAst::Opaque`] and
//! defers union normalisation to [`Type::union`]. Every frontend's
//! annotation handling routes through here, so the rules live in one
//! place rather than being duplicated per surface syntax.

use std::collections::HashMap;

use crate::types::{FuncParam, Type, TypeAst, CALLABLE_KEY};

use super::state::InferState;
use super::TypeEnv;

impl InferState {
    /// Lower a [`TypeAst`] into a [`Type`], allocating fresh type
    /// variables for opaque nodes from this state's counter.
    ///
    /// Each call uses a fresh, isolated variable scope, so any
    /// [`TypeAst::Var`] names mint independent variables. To share named
    /// variables across several expressions (e.g. all fields of a generic
    /// class), use [`InferState::lower_type_ast_scoped`] with a scope you
    /// thread across the calls.
    pub fn lower_type_ast(&mut self, ast: &TypeAst) -> Type {
        let mut scope = HashMap::new();
        self.lower_type_ast_scoped(ast, &mut scope)
    }

    /// Lower a [`TypeAst`] with `env` in scope, so a class-name reference
    /// resolves to that class's type *by scope and qualification*: a bare
    /// name binds against `env` directly; a qualified `mod.Class` resolves
    /// through the `mod` module namespace. Used for `.py` parameter /
    /// return / variable annotations, where the import environment is
    /// available. Outside such contexts (alias bodies, `.pyi` reading)
    /// `lower_type_ast` is used and class refs fall back to opaque.
    pub fn lower_type_ast_in_env(&mut self, ast: &TypeAst, env: &TypeEnv) -> Type {
        let saved = self.annotation_env.replace(env.clone());
        let mut scope = HashMap::new();
        let ty = self.lower_type_ast_scoped(ast, &mut scope);
        self.annotation_env = saved;
        ty
    }

    /// Resolve a (possibly qualified) class-name reference against the
    /// annotation env to the class's instance type. Returns `None` when
    /// there's no env in scope, the name isn't bound, the path doesn't go
    /// through module namespaces, or the binding isn't a class. `args` are
    /// the lowered type arguments from the annotation (`Box[int]`), used as
    /// the brand's parameters when present.
    fn resolve_ref_in_env(&mut self, path: &str, args: &[Type]) -> Option<Type> {
        let env = self.annotation_env.clone()?;
        let segments: Vec<&str> = path.split('.').collect();
        // Resolve the named thing: the head segment binds in `env`, and
        // each further segment is a member of the preceding namespace (an
        // `import mod` binds a row of exports; `import * as ns` a module).
        let mut cur = self.instantiate(&env.lookup(segments[0]).cloned()?);
        for seg in &segments[1..] {
            cur = self.namespace_member(&cur, seg)?;
        }
        class_instance_of(&cur, args)
    }

    /// Look up `name` as a member of a namespace value — a structural row
    /// (`import mod` → `{export: T, …}`) or a module namespace.
    fn namespace_member(&mut self, container: &Type, name: &str) -> Option<Type> {
        use crate::types::PropName;
        match container {
            Type::Row(row) => Some(row.props.get(&PropName(name.to_string()))?.ty.clone()),
            Type::Module(m) => Some(self.instantiate(&m.exports.get(name)?.clone())),
            _ => None,
        }
    }

    /// Lower a [`TypeAst`], resolving [`TypeAst::Var`] names through
    /// `scope`: the first occurrence of a name mints a fresh variable and
    /// records it, later occurrences reuse it. Threading one `scope` across
    /// multiple calls ties their shared type-variable names together.
    pub fn lower_type_ast_scoped(
        &mut self,
        ast: &TypeAst,
        scope: &mut HashMap<String, Type>,
    ) -> Type {
        match ast {
            TypeAst::Number => Type::Number,
            TypeAst::String => Type::String,
            TypeAst::Boolean => Type::Boolean,
            TypeAst::Null => Type::Null,
            TypeAst::Opaque => self.fresh_type_var(),
            TypeAst::Var(name) => {
                if let Some(ty) = scope.get(name) {
                    ty.clone()
                } else {
                    let v = self.fresh_type_var();
                    scope.insert(name.clone(), v.clone());
                    v
                }
            }
            TypeAst::Ref(name, args) => {
                let lowered_args: Vec<Type> = args
                    .iter()
                    .map(|a| self.lower_type_ast_scoped(a, scope))
                    .collect();
                match self.type_aliases.get(name).cloned() {
                    // Nominal alias: keep brand identity.
                    Some(def) if def.nominal_id.is_some() => {
                        Type::Named(def.nominal_id.unwrap(), lowered_args)
                    }
                    // Structural alias: inline its body with the type
                    // arguments substituted for the alias parameters.
                    Some(def) => {
                        let subst: std::collections::HashMap<u32, Type> =
                            def.params.iter().cloned().zip(lowered_args).collect();
                        super::type_parser::substitute_alias_body(&def.body, &subst)
                    }
                    // Not an alias: resolve the name *in scope* against the
                    // annotation env — a bare class name binds locally / by
                    // import, a qualified `mod.Class` goes through the
                    // module namespace. This brings in the class's real
                    // type only when the name is actually in scope.
                    None => self
                        .resolve_ref_in_env(name, &lowered_args)
                        // Genuinely unknown / out-of-scope name: a fresh
                        // unconstrained variable (opaque) — imposes no
                        // constraint and never a false positive.
                        .unwrap_or_else(|| self.fresh_type_var()),
                }
            }
            TypeAst::Array(elem) => Type::array(self.lower_type_ast_scoped(elem, scope)),
            TypeAst::Map(value) => Type::map(self.lower_type_ast_scoped(value, scope)),
            TypeAst::Union(members) => {
                let lowered: Vec<Type> = members
                    .iter()
                    .map(|m| self.lower_type_ast_scoped(m, scope))
                    .collect();
                Type::union(lowered)
            }
            TypeAst::Lit(value) => Type::Literal(value.clone()),
            TypeAst::Func(params, ret) => {
                let func_params = params
                    .iter()
                    .map(|p| FuncParam::required(self.lower_type_ast_scoped(p, scope)))
                    .collect();
                let ret = self.lower_type_ast_scoped(ret, scope);
                Type::wrap_callable(Type::raw_func_with_params(None, func_params, ret))
            }
        }
    }
}

/// Extract a class's *instance* type from its constructor type. A class
/// binding is a callable row `{<CALL>: (params) => Instance}` (or a bare
/// function); the instance is the call's return — `Named(id, …)` for a
/// branded class, or the instance row for an unbranded one. `args`, when
/// non-empty, replace a branded instance's parameters (an annotation like
/// `Box[int]`). Returns `None` when `ctor` isn't a constructor shape, so
/// non-class bindings don't get mistaken for types.
fn class_instance_of(ctor: &Type, args: &[Type]) -> Option<Type> {
    use crate::types::PropName;
    let func = match ctor {
        Type::Row(row) => &row.props.get(&PropName(CALLABLE_KEY.to_string()))?.ty,
        Type::Func { .. } => ctor,
        _ => return None,
    };
    let Type::Func { ret, .. } = func else {
        return None;
    };
    match ret.as_ref() {
        Type::Named(id, brand_args) => Some(Type::Named(
            *id,
            if args.is_empty() {
                brand_args.clone()
            } else {
                args.to_vec()
            },
        )),
        // Unbranded class: the instance row itself is the type.
        row @ Type::Row(_) => Some(row.clone()),
        _ => None,
    }
}
