//! Built-in types and type class constraint resolution.
//!
//! This module provides:
//! - Initial type environment with built-in functions
//! - Type class instances for Plus and Indexable
//! - Constraint solving for deferred type class predicates

use crate::error::{IntyError, TypeError};
use crate::infer::{InferState, TypeEnv};
use crate::span::Span;
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

    // Python's `isinstance(value, Class)` — accepts any value and class
    // object, returns Boolean. Its real purpose is flow-sensitive: the
    // checker recognises `isinstance(x, C)` in a branch test and narrows
    // `x` to `C`'s nominal brand (see `infer/narrow.rs`). Typed loosely so
    // the call checks regardless of argument shapes.
    env = env.extend(
        "isinstance".to_string(),
        TypeScheme::poly(
            vec![TVarName::Flex(210), TVarName::Flex(211)],
            Type::simple_func(vec![Type::flex(210), Type::flex(211)], Type::Boolean),
        ),
    );

    // `String`, `Number`, `Boolean` constructors used to live here as
    // polymorphic function bindings. Under the unified callable-row
    // design they're declared in core.d.js as callable rows so they
    // can carry static methods alongside the constructor signature
    // (`String.fromCharCode`, `Number.isInteger`, etc.) without a
    // special case in the type system. See examples/fizzy/design.md
    // § "Callable rows" + the migration in core.d.js.

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
    use crate::types::FuncParam;
    let n = Type::Number;
    let s = Type::String;
    let b = Type::Boolean;
    // Helper: build a function signature where the final parameter is
    // presence-polymorphic. Each call allocates a fresh `PVarName` so
    // distinct invocations of the same method (e.g. `s1.slice(1)` and
    // `s2.slice(0, 4)`) bind independently.
    let optional_last =
        |state: &mut InferState, required: Vec<Type>, optional: Type, ret: Type| -> Type {
            let pvar = state.fresh_pvar();
            let mut params: Vec<FuncParam> =
                required.into_iter().map(FuncParam::required).collect();
            params.push(FuncParam::optional(pvar, optional));
            Type::simple_func_with_params(params, ret)
        };
    Some(match method {
        // `indexOf(searchValue, fromIndex?)` per ECMAScript §22.1.3.8.
        // htmx hits this through chained calls without ever passing
        // the second arg, but `String.prototype.indexOf` accepts it.
        "indexOf" => optional_last(state, vec![s.clone()], n.clone(), n.clone()),
        "lastIndexOf" => optional_last(state, vec![s.clone()], n.clone(), n.clone()),
        // `substring(start, end?)`. htmx uses both 1-arg and 2-arg
        // forms in different files.
        "substring" => optional_last(state, vec![n.clone()], n.clone(), s.clone()),
        "substr" => optional_last(state, vec![n.clone()], n.clone(), s.clone()),
        // `slice(start, end?)` — the single biggest source of htmx
        // arity errors. `str.slice(-2)` and `str.slice(0, -2)` both
        // appear within the same file.
        "slice" => optional_last(state, vec![n.clone()], n.clone(), s.clone()),
        // `split(separator, limit?)`. `separator` is `String | Regex`
        // per ECMAScript. Inlined construction rather than the
        // `optional_last` helper since the first arg is a union and
        // the helper assumes a single concrete type per position.
        "split" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(Type::union(vec![s.clone(), Type::Regex])),
                    FuncParam::optional(pvar, n.clone()),
                ],
                Type::array(s.clone()),
            )
        }
        "trim" => Type::simple_func(vec![], s.clone()),
        "trimStart" => Type::simple_func(vec![], s.clone()),
        "trimEnd" => Type::simple_func(vec![], s.clone()),
        // `String.prototype.replace(pattern, replacement)`. `pattern`
        // is `String | Regex` per the ECMAScript spec; htmx hits the
        // Regex form for HTML scrubbing. Replacement could also be a
        // function in real JS but inty doesn't model that overload.
        "replace" => Type::simple_func(
            vec![Type::union(vec![s.clone(), Type::Regex]), s.clone()],
            s.clone(),
        ),
        "replaceAll" => Type::simple_func(
            vec![Type::union(vec![s.clone(), Type::Regex]), s.clone()],
            s.clone(),
        ),
        "toUpperCase" => Type::simple_func(vec![], s.clone()),
        "toLowerCase" => Type::simple_func(vec![], s.clone()),
        "charAt" => Type::simple_func(vec![n.clone()], s.clone()),
        "charCodeAt" => Type::simple_func(vec![n.clone()], n.clone()),
        // `startsWith(searchString, position?)` per §22.1.3.21;
        // `endsWith(searchString, length?)` per §22.1.3.6.
        "startsWith" => optional_last(state, vec![s.clone()], n.clone(), b.clone()),
        "endsWith" => optional_last(state, vec![s.clone()], n.clone(), b.clone()),
        "includes" => optional_last(state, vec![s.clone()], n.clone(), b.clone()),
        "repeat" => Type::simple_func(vec![n.clone()], s.clone()),
        // `padStart(targetLength, padString?)`. The default
        // padString is a single space; callers commonly omit it.
        "padStart" => optional_last(state, vec![n.clone()], s.clone(), s.clone()),
        "padEnd" => optional_last(state, vec![n.clone()], s.clone(), s.clone()),
        "concat" => Type::simple_func(vec![s.clone()], s.clone()),
        "toString" => Type::simple_func(vec![], s.clone()),
        _ => {
            let _ = (state, n, s, b);
            return None;
        }
    })
}

/// Look up a Python `str` method by name. Separate from the JavaScript
/// [`string_method_type`] surface so each language only sees its own
/// methods (issue #67); inference picks the table by `Program::language`.
pub fn python_string_method_type(state: &mut InferState, method: &str) -> Option<Type> {
    use crate::types::FuncParam;
    let n = Type::Number;
    let s = Type::String;
    let b = Type::Boolean;
    // A trailing optional parameter, allocated a fresh presence variable
    // per call so independent invocations bind separately.
    let opt_last = |state: &mut InferState, required: Vec<Type>, optional: Type, ret: Type| {
        let pvar = state.fresh_pvar();
        let mut params: Vec<FuncParam> = required.into_iter().map(FuncParam::required).collect();
        params.push(FuncParam::optional(pvar, optional));
        Type::simple_func_with_params(params, ret)
    };
    Some(match method {
        "upper" | "lower" | "title" | "capitalize" | "casefold" | "swapcase" | "strip"
        | "lstrip" | "rstrip" => {
            // Case transforms take no args; the whitespace strippers take
            // an optional set of characters. Both shapes accept a single
            // optional string argument harmlessly.
            opt_last(state, vec![], s.clone(), s.clone())
        }
        // `s.split(sep?, maxsplit?)` → list[str].
        "split" | "rsplit" => {
            let p1 = state.fresh_pvar();
            let p2 = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::optional(p1, s.clone()),
                    FuncParam::optional(p2, n.clone()),
                ],
                Type::array(s.clone()),
            )
        }
        "splitlines" => Type::simple_func(vec![], Type::array(s.clone())),
        // `sep.join(iterable)` — element type unconstrained (permissive to
        // avoid false positives on generators / maps).
        "join" => {
            let item = state.fresh_type_var();
            Type::simple_func(vec![Type::array(item)], s.clone())
        }
        "replace" => opt_last(state, vec![s.clone(), s.clone()], n.clone(), s.clone()),
        "startswith" | "endswith" => Type::simple_func(vec![s.clone()], b.clone()),
        "find" | "rfind" | "index" | "rindex" => {
            opt_last(state, vec![s.clone()], n.clone(), n.clone())
        }
        "count" => Type::simple_func(vec![s.clone()], n.clone()),
        "zfill" => Type::simple_func(vec![n.clone()], s.clone()),
        "ljust" | "rjust" | "center" => opt_last(state, vec![n.clone()], s.clone(), s.clone()),
        "expandtabs" => opt_last(state, vec![], n.clone(), s.clone()),
        "removeprefix" | "removesuffix" => Type::simple_func(vec![s.clone()], s.clone()),
        "encode" => opt_last(state, vec![], s.clone(), s.clone()),
        // `format` / `format_map` are variadic / dynamic; accept any call.
        "format" | "format_map" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![FuncParam::optional(pvar, state.fresh_type_var())],
                s.clone(),
            )
        }
        "isdigit" | "isalpha" | "isalnum" | "isspace" | "isupper" | "islower" | "istitle"
        | "isnumeric" | "isdecimal" | "isidentifier" | "isprintable" => {
            Type::simple_func(vec![], b.clone())
        }
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
        "exec" => Type::simple_func(vec![s.clone()], Type::array(s.clone())),
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
    use crate::types::FuncParam;
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
        // `Array.prototype.indexOf(searchElement, fromIndex?)`.
        "indexOf" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(pvar, n.clone()),
                ],
                n.clone(),
            )
        }
        "lastIndexOf" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(pvar, n.clone()),
                ],
                n.clone(),
            )
        }
        "includes" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(pvar, n.clone()),
                ],
                b.clone(),
            )
        }
        // `Array.prototype.slice(start?, end?)` — both optional.
        // Two presence vars, one per optional position. Note this is
        // a different shape from `String.prototype.slice` (which has
        // a required first arg in practical usage and inty's model).
        "slice" => {
            let p1 = state.fresh_pvar();
            let p2 = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::optional(p1, n.clone()),
                    FuncParam::optional(p2, n.clone()),
                ],
                arr.clone(),
            )
        }
        "concat" => Type::simple_func(vec![arr.clone()], arr.clone()),
        // `Array.prototype.join(separator?)` — separator defaults to
        // ','. Most array→string conversions in real code omit it.
        "join" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(vec![FuncParam::optional(pvar, s.clone())], s.clone())
        }
        "reverse" => Type::simple_func(vec![], arr.clone()),
        "sort" => Type::simple_func(vec![], arr.clone()),
        "fill" => Type::simple_func(vec![elem.clone()], arr.clone()),
        // Returns `T | undefined` — the predicate may match nothing, in
        // which case the runtime returns `undefined`. Forces the caller
        // through narrowing before they can use the result, which is
        // the user-visible payoff that closes the loop on phase 1.
        //
        // Callback parameter types use `callable_row_open` so callers
        // can pass any callable value — including constructors with
        // statics, e.g. `arr.find(String)` — via row polymorphism.
        "find" => Type::simple_func(
            vec![state.callable_row_open(None, vec![elem.clone()], b.clone())],
            Type::union(vec![elem.clone(), Type::Undefined]),
        ),
        "findIndex" => Type::simple_func(
            vec![state.callable_row_open(None, vec![elem.clone()], b.clone())],
            n.clone(),
        ),
        "forEach" => Type::simple_func(
            vec![state.callable_row_open(None, vec![elem.clone()], u.clone())],
            u.clone(),
        ),
        "filter" => Type::simple_func(
            vec![state.callable_row_open(None, vec![elem.clone()], b.clone())],
            arr.clone(),
        ),
        "some" => Type::simple_func(
            vec![state.callable_row_open(None, vec![elem.clone()], b.clone())],
            b.clone(),
        ),
        "every" => Type::simple_func(
            vec![state.callable_row_open(None, vec![elem.clone()], b.clone())],
            b.clone(),
        ),
        // Polymorphic: map produces an array of a fresh element type U.
        "map" => {
            let u_var = state.fresh_type_var();
            let cb = state.callable_row_open(None, vec![elem.clone()], u_var.clone());
            Type::simple_func(vec![cb], Type::array(u_var))
        }
        // Polymorphic: reduce carries an accumulator of a fresh type U.
        "reduce" => {
            let u_var = state.fresh_type_var();
            let cb =
                state.callable_row_open(None, vec![u_var.clone(), elem.clone()], u_var.clone());
            Type::simple_func(vec![cb, u_var.clone()], u_var)
        }
        "reduceRight" => {
            let u_var = state.fresh_type_var();
            let cb =
                state.callable_row_open(None, vec![u_var.clone(), elem.clone()], u_var.clone());
            Type::simple_func(vec![cb, u_var.clone()], u_var)
        }
        "toString" => Type::simple_func(vec![], s.clone()),
        _ => {
            let _ = (n, s, b, u, arr);
            return None;
        }
    })
}

/// Look up a Python `list` method by name for a list whose element type
/// is `elem`. Separate from the JavaScript [`array_method_type`] surface
/// (issue #67); inference picks the table by `Program::language`. In-place
/// mutators return `None` (modelled as the language unit `Null`).
pub fn python_list_method_type(state: &mut InferState, elem: &Type, method: &str) -> Option<Type> {
    use crate::types::FuncParam;
    let n = Type::Number;
    let nil = Type::Null;
    let arr = Type::array(elem.clone());
    Some(match method {
        "append" => Type::simple_func(vec![elem.clone()], nil.clone()),
        "extend" => Type::simple_func(vec![arr.clone()], nil.clone()),
        "insert" => Type::simple_func(vec![n.clone(), elem.clone()], nil.clone()),
        "remove" => Type::simple_func(vec![elem.clone()], nil.clone()),
        // `pop(index?)` returns the removed element.
        "pop" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(vec![FuncParam::optional(pvar, n.clone())], elem.clone())
        }
        // `index(x, start?, stop?)`.
        "index" => {
            let p1 = state.fresh_pvar();
            let p2 = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(p1, n.clone()),
                    FuncParam::optional(p2, n.clone()),
                ],
                n.clone(),
            )
        }
        "count" => Type::simple_func(vec![elem.clone()], n.clone()),
        "sort" | "reverse" | "clear" => Type::simple_func(vec![], nil.clone()),
        "copy" => Type::simple_func(vec![], arr.clone()),
        _ => {
            let _ = (state, n, nil, arr);
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
            let cb =
                state.callable_row_open(None, vec![inner.clone()], Type::promise(u_var.clone()));
            Type::simple_func(vec![cb], Type::promise(u_var))
        }
        "catch" => {
            // (error -> Promise<T>) -> Promise<T>. error is a fresh var
            // since inty has no single "Error" type.
            let err_var = state.fresh_type_var();
            let cb = state.callable_row_open(None, vec![err_var], Type::promise(inner.clone()));
            Type::simple_func(vec![cb], Type::promise(inner.clone()))
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
        // Error sentinel satisfies every constraint trivially. The
        // type that flowed in already failed inference; making its
        // dependent uses fail their type-class checks too would
        // produce one noise diagnostic per use site.
        if pred
            .types
            .iter()
            .any(|t| matches!(self.apply_subst(t), Type::Error))
        {
            return Ok(());
        }
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

            // Error satisfies trivially; the original failure was
            // already reported.
            Type::Error => Ok(()),

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
        // `Array` and `Object` constructors stay in the Rust env
        // (Array is polymorphic; both are special-cased by inference).
        // `String` / `Number` / `Boolean` moved to core.d.js as
        // callable rows so they can carry static methods alongside
        // the constructor signature.
        assert!(env.lookup("Array").is_some());
        assert!(env.lookup("Object").is_some());
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
