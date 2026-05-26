//! Lowering of the frontend-neutral [`TypeAst`] IR into a concrete
//! [`Type`].
//!
//! This is the single semantic home for turning a parsed type expression
//! into an inty type: it mints fresh variables for [`TypeAst::Opaque`] and
//! defers union normalisation to [`Type::union`]. Every frontend's
//! annotation handling routes through here, so the rules live in one
//! place rather than being duplicated per surface syntax.

use crate::types::{FuncParam, Type, TypeAst};

use super::state::InferState;

impl InferState {
    /// Lower a [`TypeAst`] into a [`Type`], allocating fresh type
    /// variables for opaque nodes from this state's counter.
    pub fn lower_type_ast(&mut self, ast: &TypeAst) -> Type {
        match ast {
            TypeAst::Number => Type::Number,
            TypeAst::String => Type::String,
            TypeAst::Boolean => Type::Boolean,
            TypeAst::Null => Type::Null,
            TypeAst::Opaque => self.fresh_type_var(),
            TypeAst::Array(elem) => Type::array(self.lower_type_ast(elem)),
            TypeAst::Map(value) => Type::map(self.lower_type_ast(value)),
            TypeAst::Union(members) => {
                let lowered: Vec<Type> = members.iter().map(|m| self.lower_type_ast(m)).collect();
                Type::union(lowered)
            }
            TypeAst::Lit(value) => Type::Literal(value.clone()),
            TypeAst::Func(params, ret) => {
                let func_params = params
                    .iter()
                    .map(|p| FuncParam::required(self.lower_type_ast(p)))
                    .collect();
                let ret = self.lower_type_ast(ret);
                Type::wrap_callable(Type::raw_func_with_params(None, func_params, ret))
            }
        }
    }
}
