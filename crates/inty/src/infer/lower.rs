//! Lowering of the frontend-neutral [`TypeAst`] IR into a concrete
//! [`Type`].
//!
//! This is the single semantic home for turning a parsed type expression
//! into an inty type: it mints fresh variables for [`TypeAst::Opaque`] and
//! defers union normalisation to [`Type::union`]. Every frontend's
//! annotation handling routes through here, so the rules live in one
//! place rather than being duplicated per surface syntax.

use std::collections::HashMap;

use crate::types::{FuncParam, Type, TypeAst};

use super::state::InferState;

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
                    // Unknown name: a fresh unconstrained variable, exactly
                    // as an unmodelled (opaque) type — imposes no constraint.
                    None => self.fresh_type_var(),
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
