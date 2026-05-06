//! Built-in types and type class constraint resolution.
//!
//! This module provides:
//! - Initial type environment with built-in functions
//! - Type class instances for Plus and Indexable
//! - Constraint solving for deferred type class predicates

use crate::error::{IntyError, TypeError};
use crate::infer::{InferState, TypeEnv};
use crate::lexer::Span;
use crate::types::{ClassName, RowType, TVarName, Type, TypePred, TypeScheme};

/// Create the initial type environment with built-in bindings.
///
/// Only bindings that need to be truly polymorphic (each lookup instantiates
/// fresh type variables) live here. Non-polymorphic bindings — `console`,
/// `Math`, `JSON`, `parseInt`, `parseFloat`, `isNaN`, `isFinite` and the DOM
/// surface — are declared in `stdlib/*.d.js` and loaded via
/// [`crate::stdlib::initial_env_with_stdlib`].
pub fn initial_env() -> TypeEnv {
    let mut env = TypeEnv::empty();

    // undefined and null are keywords, but we can add them as values too
    env = env.extend("undefined".to_string(), TypeScheme::mono(Type::Undefined));

    // Array constructor (simplified)
    env = env.extend(
        "Array".to_string(),
        TypeScheme::poly(
            vec![TVarName::Flex(200)],
            Type::simple_func(vec![], Type::array(Type::flex(200))),
        ),
    );

    // Object constructor
    env = env.extend(
        "Object".to_string(),
        TypeScheme::mono(Type::simple_func(
            vec![],
            Type::Row(RowType::empty_closed()),
        )),
    );

    // String constructor: converts any value to string
    env = env.extend(
        "String".to_string(),
        TypeScheme::poly(
            vec![TVarName::Flex(201)],
            Type::simple_func(vec![Type::flex(201)], Type::String),
        ),
    );

    // Number constructor: converts any value to number
    env = env.extend(
        "Number".to_string(),
        TypeScheme::poly(
            vec![TVarName::Flex(202)],
            Type::simple_func(vec![Type::flex(202)], Type::Number),
        ),
    );

    // Boolean constructor: converts any value to boolean
    env = env.extend(
        "Boolean".to_string(),
        TypeScheme::poly(
            vec![TVarName::Flex(203)],
            Type::simple_func(vec![Type::flex(203)], Type::Boolean),
        ),
    );

    env
}

/// Look up a built-in String prototype method by name.
///
/// Returns a fresh function type each call: for polymorphic methods the
/// caller can unify the type variables with concrete argument types
/// without affecting other call sites. For monomorphic methods the
/// types are constants (no vars to freshen).
///
/// Used from `infer_member_from_type` when a property is accessed on a
/// value of type `String`.
pub fn string_method_type(state: &mut InferState, method: &str) -> Option<Type> {
    let n = Type::Number;
    let s = Type::String;
    let b = Type::Boolean;
    Some(match method {
        "indexOf" => Type::simple_func(vec![s.clone()], n.clone()),
        "lastIndexOf" => Type::simple_func(vec![s.clone()], n.clone()),
        "substring" => Type::simple_func(vec![n.clone(), n.clone()], s.clone()),
        "substr" => Type::simple_func(vec![n.clone(), n.clone()], s.clone()),
        "slice" => Type::simple_func(vec![n.clone(), n.clone()], s.clone()),
        "split" => Type::simple_func(vec![s.clone()], Type::array(s.clone())),
        "trim" => Type::simple_func(vec![], s.clone()),
        "trimStart" => Type::simple_func(vec![], s.clone()),
        "trimEnd" => Type::simple_func(vec![], s.clone()),
        "replace" => Type::simple_func(vec![s.clone(), s.clone()], s.clone()),
        "replaceAll" => Type::simple_func(vec![s.clone(), s.clone()], s.clone()),
        "toUpperCase" => Type::simple_func(vec![], s.clone()),
        "toLowerCase" => Type::simple_func(vec![], s.clone()),
        "charAt" => Type::simple_func(vec![n.clone()], s.clone()),
        "charCodeAt" => Type::simple_func(vec![n.clone()], n.clone()),
        "startsWith" => Type::simple_func(vec![s.clone()], b.clone()),
        "endsWith" => Type::simple_func(vec![s.clone()], b.clone()),
        "includes" => Type::simple_func(vec![s.clone()], b.clone()),
        "repeat" => Type::simple_func(vec![n.clone()], s.clone()),
        "padStart" => Type::simple_func(vec![n.clone(), s.clone()], s.clone()),
        "padEnd" => Type::simple_func(vec![n.clone(), s.clone()], s.clone()),
        "concat" => Type::simple_func(vec![s.clone()], s.clone()),
        "toString" => Type::simple_func(vec![], s.clone()),
        _ => {
            let _ = (state, n, s, b);
            return None;
        }
    })
}

/// Look up a built-in Regex prototype method by name. Each call gets a
/// fresh function type. `test` returns Boolean; `match`/`exec` return
/// the match-info row directly (without modelling the "no match"
/// `null` fallback, which would require nullable types).
pub fn regex_method_type(state: &mut InferState, method: &str) -> Option<Type> {
    let _ = state;
    let s = Type::String;
    let n = Type::Number;
    let b = Type::Boolean;
    Some(match method {
        "test" => Type::simple_func(vec![s.clone()], b.clone()),
        "exec" => Type::simple_func(
            vec![s.clone()],
            Type::array(s.clone()),
        ),
        "toString" => Type::simple_func(vec![], s.clone()),
        // Direct properties.
        "source" => s.clone(),
        "flags" => s.clone(),
        "global" => b.clone(),
        "ignoreCase" => b.clone(),
        "multiline" => b.clone(),
        "sticky" => b.clone(),
        "unicode" => b.clone(),
        "lastIndex" => n.clone(),
        _ => {
            let _ = (s, n, b);
            return None;
        }
    })
}

/// Look up a built-in Array prototype method by name for an array whose
/// element type is `elem`.
///
/// Polymorphic methods like `map` and `reduce` get fresh type variables
/// from the caller's `InferState`; unification during the surrounding
/// call expression binds them.
pub fn array_method_type(state: &mut InferState, elem: &Type, method: &str) -> Option<Type> {
    let n = Type::Number;
    let s = Type::String;
    let b = Type::Boolean;
    let u = Type::Undefined;
    let arr = Type::array(elem.clone());
    Some(match method {
        "push" => Type::simple_func(vec![elem.clone()], n.clone()),
        "pop" => Type::simple_func(vec![], elem.clone()),
        "shift" => Type::simple_func(vec![], elem.clone()),
        "unshift" => Type::simple_func(vec![elem.clone()], n.clone()),
        "indexOf" => Type::simple_func(vec![elem.clone()], n.clone()),
        "lastIndexOf" => Type::simple_func(vec![elem.clone()], n.clone()),
        "includes" => Type::simple_func(vec![elem.clone()], b.clone()),
        "slice" => Type::simple_func(vec![n.clone(), n.clone()], arr.clone()),
        "concat" => Type::simple_func(vec![arr.clone()], arr.clone()),
        "join" => Type::simple_func(vec![s.clone()], s.clone()),
        "reverse" => Type::simple_func(vec![], arr.clone()),
        "sort" => Type::simple_func(vec![], arr.clone()),
        "fill" => Type::simple_func(vec![elem.clone()], arr.clone()),
        // Returns `T | undefined` — the predicate may match nothing, in
        // which case the runtime returns `undefined`. Forces the caller
        // through narrowing before they can use the result, which is
        // the user-visible payoff that closes the loop on phase 1.
        "find" => Type::simple_func(
            vec![Type::simple_func(vec![elem.clone()], b.clone())],
            Type::union(vec![elem.clone(), Type::Undefined]),
        ),
        "findIndex" => Type::simple_func(
            vec![Type::simple_func(vec![elem.clone()], b.clone())],
            n.clone(),
        ),
        "forEach" => Type::simple_func(
            vec![Type::simple_func(vec![elem.clone()], u.clone())],
            u.clone(),
        ),
        "filter" => Type::simple_func(
            vec![Type::simple_func(vec![elem.clone()], b.clone())],
            arr.clone(),
        ),
        "some" => Type::simple_func(
            vec![Type::simple_func(vec![elem.clone()], b.clone())],
            b.clone(),
        ),
        "every" => Type::simple_func(
            vec![Type::simple_func(vec![elem.clone()], b.clone())],
            b.clone(),
        ),
        // Polymorphic: map produces an array of a fresh element type U.
        "map" => {
            let u_var = state.fresh_type_var();
            Type::simple_func(
                vec![Type::simple_func(vec![elem.clone()], u_var.clone())],
                Type::array(u_var),
            )
        }
        // Polymorphic: reduce carries an accumulator of a fresh type U.
        "reduce" => {
            let u_var = state.fresh_type_var();
            Type::simple_func(
                vec![
                    Type::simple_func(vec![u_var.clone(), elem.clone()], u_var.clone()),
                    u_var.clone(),
                ],
                u_var,
            )
        }
        "reduceRight" => {
            let u_var = state.fresh_type_var();
            Type::simple_func(
                vec![
                    Type::simple_func(vec![u_var.clone(), elem.clone()], u_var.clone()),
                    u_var.clone(),
                ],
                u_var,
            )
        }
        "toString" => Type::simple_func(vec![], s.clone()),
        _ => {
            let _ = (n, s, b, u, arr);
            return None;
        }
    })
}

/// Look up a built-in Promise prototype method.
///
/// `inner` is the `T` in `Promise<T>`. Each call produces a fresh function
/// type so call sites don't unify their result types together.
///
/// `.then` here commits to the "callback must return a Promise" shape
/// (`(T) => Promise<U>) => Promise<U>`) rather than the JS-spec
/// `(T) => U | Promise<U>` form, because inty has no union types.
/// Users passing a plain-value callback should return `Promise.resolve(v)`
/// or make the function `async`.
pub fn promise_method_type(state: &mut InferState, inner: &Type, method: &str) -> Option<Type> {
    Some(match method {
        "then" => {
            let u_var = state.fresh_type_var();
            Type::simple_func(
                vec![Type::simple_func(
                    vec![inner.clone()],
                    Type::promise(u_var.clone()),
                )],
                Type::promise(u_var),
            )
        }
        "catch" => {
            // (error -> Promise<T>) -> Promise<T>. error is a fresh var
            // since inty has no single "Error" type.
            let err_var = state.fresh_type_var();
            Type::simple_func(
                vec![Type::simple_func(
                    vec![err_var],
                    Type::promise(inner.clone()),
                )],
                Type::promise(inner.clone()),
            )
        }
        "finally" => Type::simple_func(
            vec![Type::simple_func(vec![], Type::Undefined)],
            Type::promise(inner.clone()),
        ),
        _ => return None,
    })
}

impl InferState {
    /// Resolve pending type class constraints.
    /// This should be called after inference to check that all constraints are satisfiable.
    pub fn resolve_constraints(&mut self) -> Result<(), IntyError> {
        let constraints = std::mem::take(&mut self.pending_constraints);

        for constraint in constraints {
            self.resolve_constraint(&constraint.pred, constraint.span)?;
        }

        Ok(())
    }

    /// Resolve a single type class constraint.
    fn resolve_constraint(&mut self, pred: &TypePred, span: Span) -> Result<(), IntyError> {
        match pred.class {
            ClassName::Plus => self.resolve_plus(&pred.types[0], span),
            ClassName::Indexable => {
                self.resolve_indexable(&pred.types[0], &pred.types[1], &pred.types[2], span)
            }
        }
    }

    /// Resolve Plus constraint: type must be Number or String.
    fn resolve_plus(&mut self, ty: &Type, span: Span) -> Result<(), IntyError> {
        let ty = self.apply_subst(ty);

        match &ty {
            Type::Number | Type::String => Ok(()),

            Type::Var(TVarName::Flex(_)) => {
                // Keep the constraint - don't default to Number
                Ok(())
            }

            Type::Var(TVarName::Skolem(_)) => {
                // Skolem variables can't be resolved
                Err(TypeError::ConstraintNotSatisfied {
                    class: "Plus".to_string(),
                    ty: ty.to_string(),
                    span,
                }
                .into())
            }

            _ => Err(TypeError::ConstraintNotSatisfied {
                class: "Plus".to_string(),
                ty: ty.to_string(),
                span,
            }
            .into()),
        }
    }

    /// Resolve Indexable constraint: container[index] = element.
    fn resolve_indexable(
        &mut self,
        container: &Type,
        index: &Type,
        element: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        let container = self.apply_subst(container);
        let index = self.apply_subst(index);
        let element = self.apply_subst(element);

        match &container {
            // Array indexing: [T][Number] = T
            Type::Array(elem_ty) => {
                self.unify(span, &index, &Type::Number)?;
                self.unify(span, &element, elem_ty)?;
                Ok(())
            }

            // String indexing: String[Number] = String
            Type::String => {
                self.unify(span, &index, &Type::Number)?;
                self.unify(span, &element, &Type::String)?;
                Ok(())
            }

            // Map indexing: Map<T>[String] = T
            Type::Map(value_ty) => {
                self.unify(span, &index, &Type::String)?;
                self.unify(span, &element, value_ty)?;
                Ok(())
            }

            // Object indexing with string key
            Type::Row(row) => {
                // Check if this row could be array-like (only has array properties like `length`)
                let is_array_like = row.props.keys().all(|k| k.0 == "length");

                if is_array_like && matches!(row.tail, crate::types::RowTail::Open(_)) {
                    // This looks like an array constraint - try array-style indexing
                    // Create a fresh element type and unify the row with Array<elem>
                    let elem_var = self.fresh_type_var();
                    let array_type = Type::array(elem_var.clone());

                    // Try to unify the row with the array's structural representation
                    // This will succeed if the row is compatible with arrays
                    if self.unify(span, &container, &array_type).is_ok() {
                        self.unify(span, &index, &Type::Number)?;
                        self.unify(span, &element, &elem_var)?;
                        return Ok(());
                    }
                }

                // Fall back to object indexing with string key
                self.unify(span, &index, &Type::String)?;

                // The element type is the union of all property types
                // For simplicity, we use a fresh variable
                // In a full implementation, we'd need union types
                Ok(())
            }

            Type::Var(TVarName::Flex(_)) => {
                // Keep the constraint - don't default to Array
                Ok(())
            }

            _ => Err(TypeError::ConstraintNotSatisfied {
                class: "Indexable".to_string(),
                ty: container.to_string(),
                span,
            }
            .into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_env() {
        let env = initial_env();
        // Polymorphic primitives live in the Rust env; library-shaped
        // bindings have moved to stdlib/*.d.js.
        assert!(env.lookup("Array").is_some());
        assert!(env.lookup("String").is_some());
        assert!(env.lookup("Number").is_some());
        assert!(env.lookup("undefined").is_some());
    }

    #[test]
    fn test_resolve_plus_number() {
        let mut state = InferState::new();
        assert!(state.resolve_plus(&Type::Number, Span::new(0, 0)).is_ok());
    }

    #[test]
    fn test_resolve_plus_string() {
        let mut state = InferState::new();
        assert!(state.resolve_plus(&Type::String, Span::new(0, 0)).is_ok());
    }

    #[test]
    fn test_resolve_plus_variable() {
        let mut state = InferState::new();
        let var = Type::flex(0);
        assert!(state.resolve_plus(&var, Span::new(0, 0)).is_ok());
        // Type variable should be kept (not defaulted) to preserve polymorphism
        assert_eq!(state.apply_subst(&var), var);
    }

    #[test]
    fn test_resolve_indexable_array() {
        let mut state = InferState::new();
        let arr = Type::array(Type::Number);
        let elem = Type::flex(0);
        assert!(state
            .resolve_indexable(&arr, &Type::Number, &elem, Span::new(0, 0))
            .is_ok());
        assert_eq!(state.apply_subst(&elem), Type::Number);
    }

    #[test]
    fn test_resolve_indexable_array_like_row() {
        use crate::types::TVarName;

        let mut state = InferState::new();
        // {length: Number | a} should be indexable like an array with Number index
        let row = Type::object_open([("length", Type::Number)], TVarName::Flex(0));
        let index = Type::flex(1);
        let elem = Type::flex(2);

        assert!(state
            .resolve_indexable(&row, &index, &elem, Span::new(0, 0))
            .is_ok());

        // The index should be Number (array-style) not String (object-style)
        assert_eq!(state.apply_subst(&index), Type::Number);
    }

    #[test]
    fn test_resolve_indexable_object_row() {
        let mut state = InferState::new();
        // {foo: String, bar: Number} is NOT array-like, should use string indexing
        let row = Type::object([("foo", Type::String), ("bar", Type::Number)]);
        let index = Type::flex(0);
        let elem = Type::flex(1);

        assert!(state
            .resolve_indexable(&row, &index, &elem, Span::new(0, 0))
            .is_ok());

        // Index should be string for object access
        assert_eq!(state.apply_subst(&index), Type::String);
    }
}
