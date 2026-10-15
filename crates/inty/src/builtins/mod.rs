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
    js_string_method_type(state, method).map(|t| with_receiver(t, Type::String))
}

/// A built-in method's type with its receiver as `this`. A method read
/// off a value and then called on its own (`const g = s.slice; g()`)
/// is then a free call with `this` undefined — the TypeError it is in
/// JavaScript — like a detached user-defined method.
fn with_receiver(ty: Type, receiver: Type) -> Type {
    use crate::types::{PropName, CALLABLE_KEY};
    match ty {
        Type::Func {
            this_type: None,
            params,
            ret,
        } => Type::Func {
            this_type: Some(Box::new(receiver)),
            params,
            ret,
        },
        // A callable row: its call signature.
        Type::Row(mut row) => {
            let key = PropName(CALLABLE_KEY.to_string());
            if let Some(entry) = row.props.remove(&key) {
                let mut entry = entry;
                entry.ty = with_receiver(entry.ty, receiver);
                row.props.insert(key, entry);
            }
            Type::Row(row)
        }
        other => other,
    }
}

fn js_string_method_type(state: &mut InferState, method: &str) -> Option<Type> {
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
        "indexOf" => optional_last(state, vec![s.clone()], n.clone(), Type::Number),
        "lastIndexOf" => optional_last(state, vec![s.clone()], n.clone(), Type::Number),
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
        "charCodeAt" => Type::simple_func(vec![n.clone()], Type::Number),
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
        // `match(re)`: the whole match and the capture groups, or `null`
        // when nothing matches (so the result must be checked). A group
        // that didn't participate reads as `undefined` at runtime but is
        // typed `String`, as elsewhere for array reads.
        "match" => Type::simple_func(
            vec![Type::union(vec![s.clone(), Type::Regex])],
            Type::union(vec![Type::array(s.clone()), Type::Null]),
        ),
        // `matchAll(re)`: one such array per match (an iterator in
        // JavaScript; an array here, which `for … of` and spreading
        // treat alike).
        "matchAll" => Type::simple_func(
            vec![Type::union(vec![s.clone(), Type::Regex])],
            Type::array(Type::array(s.clone())),
        ),
        "search" => Type::simple_func(
            vec![Type::union(vec![s.clone(), Type::Regex])],
            Type::Number,
        ),
        "localeCompare" => Type::simple_func(vec![s.clone()], n.clone()),
        "at" => Type::simple_func(
            vec![Type::Number],
            Type::union(vec![s.clone(), Type::Undefined]),
        ),
        "codePointAt" => Type::simple_func(vec![Type::Number], Type::Number),
        "normalize" => optional_last(state, vec![], s.clone(), s.clone()),
        _ => {
            let _ = (state, n, s, b);
            return None;
        }
    })
}

/// Look up a `Number.prototype` method by name (JavaScript), with the
/// number as its receiver. Each optional argument gets its own presence
/// variable per read, as for strings, so `n.toString()` and
/// `n.toString(16)` both check.
pub fn number_method_type(state: &mut InferState, method: &str) -> Option<Type> {
    use crate::types::FuncParam;
    let n = Type::Number;
    let s = Type::String;
    let optional_only = |state: &mut InferState, optional: Type, ret: Type| -> Type {
        let pvar = state.fresh_pvar();
        Type::simple_func_with_params(vec![FuncParam::optional(pvar, optional)], ret)
    };
    let ty = match method {
        // `toFixed(digits?)`, `toPrecision(precision?)`,
        // `toExponential(fractionDigits?)`, `toString(radix?)`
        // (ECMAScript §21.1.3).
        "toFixed" | "toPrecision" | "toExponential" | "toString" => {
            optional_only(state, n.clone(), s.clone())
        }
        // `toLocaleString(locales?)`: the options argument isn't modelled.
        "toLocaleString" => optional_only(state, s.clone(), s.clone()),
        "valueOf" => Type::simple_func(vec![], n.clone()),
        _ => return None,
    };
    Some(with_receiver(ty, Type::Number))
}

/// Look up a `Boolean.prototype` method by name (JavaScript).
pub fn boolean_method_type(method: &str) -> Option<Type> {
    let ty = match method {
        "toString" => Type::simple_func(vec![], Type::String),
        "valueOf" => Type::simple_func(vec![], Type::Boolean),
        _ => return None,
    };
    Some(with_receiver(ty, Type::Boolean))
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

/// The members of a typed array (`Int32Array`, …) that inty knows. A
/// typed array has a fixed length, so it has no `push`/`pop`.
pub fn typed_array_member_type(
    state: &mut InferState,
    kind: crate::types::TypedArrayKind,
    member: &str,
) -> Option<Type> {
    use crate::types::FuncParam;
    let this = Type::TypedArray(kind);
    Some(match member {
        "length" | "byteLength" | "byteOffset" => Type::Number,
        "fill" => Type::simple_func(vec![kind.element()], this),
        // `subarray(start?, end?)` views the same buffer; `slice` copies.
        "subarray" | "slice" => {
            let (p1, p2) = (state.fresh_pvar(), state.fresh_pvar());
            Type::simple_func_with_params(
                vec![
                    FuncParam::optional(p1, Type::Number),
                    FuncParam::optional(p2, Type::Number),
                ],
                this,
            )
        }
        // `set(source, offset?)`: copy another array of the same kind in.
        "set" => {
            let p = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(this),
                    FuncParam::optional(p, Type::Number),
                ],
                Type::Undefined,
            )
        }
        // The stdlib's `ArrayBuffer`.
        "buffer" => {
            let def = state.type_aliases.get("ArrayBuffer")?;
            match def.rec_id {
                Some(id) => Type::Named(id, Vec::new()),
                None => def.body.clone(),
            }
        }
        _ => return None,
    })
}

/// How many inserted items `Array.prototype.splice` accepts (see
/// [`array_method_type`]).
pub const SPLICE_MAX_ITEMS: usize = 4;

/// Look up a built-in Array prototype method by name for an array whose
/// element type is `elem`.
///
/// Polymorphic methods like `map` and `reduce` get fresh type variables
/// from the caller's `InferState`; unification during the surrounding
/// call expression binds them.
pub fn array_method_type(state: &mut InferState, elem: &Type, method: &str) -> Option<Type> {
    js_array_method_type(state, elem, method).map(|t| with_receiver(t, Type::array(elem.clone())))
}

/// An iteration callback `(elem, index?, array?) => ret`: what `map`,
/// `filter`, `forEach`, … pass it.
fn element_callback(state: &mut InferState, elem: &Type, ret: Type) -> Type {
    use crate::types::FuncParam;
    let (p1, p2) = (state.fresh_pvar(), state.fresh_pvar());
    state.callable_row_open_with_params(
        vec![
            FuncParam::required(elem.clone()),
            FuncParam::optional(p1, Type::Number),
            FuncParam::optional(p2, Type::array(elem.clone())),
        ],
        ret,
    )
}

fn js_array_method_type(state: &mut InferState, elem: &Type, method: &str) -> Option<Type> {
    use crate::types::FuncParam;
    let n = Type::Number;
    let s = Type::String;
    let b = Type::Boolean;
    let u = Type::Undefined;
    let arr = Type::array(elem.clone());
    Some(match method {
        "push" => Type::simple_func(vec![elem.clone()], Type::Number),
        "pop" => Type::simple_func(vec![], elem.clone()),
        "shift" => Type::simple_func(vec![], elem.clone()),
        "unshift" => Type::simple_func(vec![elem.clone()], Type::Number),
        // `Array.prototype.splice(start, deleteCount?, ...items)`, returning
        // the removed elements. There are no variadic function types, so
        // the items are modelled as SPLICE_MAX_ITEMS optional parameters
        // (a call inserting more is rejected, never mistyped).
        "splice" => {
            let mut params = vec![FuncParam::required(n.clone())];
            params.push(FuncParam::optional(state.fresh_pvar(), n.clone()));
            for _ in 0..SPLICE_MAX_ITEMS {
                params.push(FuncParam::optional(state.fresh_pvar(), elem.clone()));
            }
            Type::simple_func_with_params(params, arr.clone())
        }
        // `Array.prototype.indexOf(searchElement, fromIndex?)`.
        "indexOf" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(pvar, n.clone()),
                ],
                Type::Number,
            )
        }
        "lastIndexOf" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(pvar, n.clone()),
                ],
                Type::Number,
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
        // `sort(compare?)`: the comparator's sign orders two elements.
        "sort" => {
            let pvar = state.fresh_pvar();
            let cmp = state.callable_row_open(None, vec![elem.clone(), elem.clone()], Type::Number);
            Type::simple_func_with_params(vec![FuncParam::optional(pvar, cmp)], arr.clone())
        }
        "fill" => Type::simple_func(vec![elem.clone()], arr.clone()),
        // Returns `T | undefined` — the predicate may match nothing, in
        // which case the runtime returns `undefined`. Forces the caller
        // through narrowing before they can use the result, which is
        // the user-visible payoff that closes the loop on phase 1.
        //
        // Callback parameter types are open callable rows so callers
        // can pass any callable value — including constructors with
        // statics, e.g. `arr.find(String)` — via row polymorphism.
        // Every iteration callback is also passed the index and the
        // array (`xs.map((x, i) => …)`); those parameters are optional,
        // so a function taking only the element fits too.
        "find" => Type::simple_func(
            vec![element_callback(state, elem, b.clone())],
            Type::union(vec![elem.clone(), Type::Undefined]),
        ),
        // `Array.prototype.at(index)`: the element at `index`, counted
        // from the end if negative, or `undefined` outside the array.
        "at" => Type::simple_func(
            vec![n.clone()],
            Type::union(vec![elem.clone(), Type::Undefined]),
        ),
        "findIndex" => {
            Type::simple_func(vec![element_callback(state, elem, b.clone())], Type::Number)
        }
        "forEach" => Type::simple_func(vec![element_callback(state, elem, u.clone())], u.clone()),
        "filter" => Type::simple_func(vec![element_callback(state, elem, b.clone())], arr.clone()),
        "some" => Type::simple_func(vec![element_callback(state, elem, b.clone())], b.clone()),
        "every" => Type::simple_func(vec![element_callback(state, elem, b.clone())], b.clone()),
        // Polymorphic: map produces an array of a fresh element type U.
        "map" => {
            let u_var = state.fresh_type_var();
            let cb = element_callback(state, elem, u_var.clone());
            Type::simple_func(vec![cb], Type::array(u_var))
        }
        // Polymorphic: reduce carries an accumulator of a fresh type U.
        "reduce" | "reduceRight" => {
            let u_var = state.fresh_type_var();
            let (p1, p2) = (state.fresh_pvar(), state.fresh_pvar());
            let cb = state.callable_row_open_with_params(
                vec![
                    FuncParam::required(u_var.clone()),
                    FuncParam::required(elem.clone()),
                    FuncParam::optional(p1, Type::Number),
                    FuncParam::optional(p2, arr.clone()),
                ],
                u_var.clone(),
            );
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
                Type::Number,
            )
        }
        "count" => Type::simple_func(vec![elem.clone()], Type::Number),
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
/// A `then` / `catch` callback may return a value or a promise of one
/// (`(T) => U | Promise<U>`); the promise the call returns is flattened
/// either way. The callback's result is a fresh variable `r`, recorded in
/// `promise_results` with the `U` it determines; `infer_call` settles
/// the pair once the callback has been checked (`settle_promise_results`).
pub fn promise_method_type(state: &mut InferState, inner: &Type, method: &str) -> Option<Type> {
    Some(match method {
        "then" => {
            let u_var = state.fresh_type_var();
            let r_var = state.fresh_type_var();
            state.promise_results.push((r_var.clone(), u_var.clone()));
            let cb = state.callable_row_open(None, vec![inner.clone()], r_var);
            Type::simple_func(vec![cb], Type::promise(u_var))
        }
        "catch" => {
            // (error) => T | Promise<T>. error is a fresh var since inty
            // has no single "Error" type.
            let err_var = state.fresh_type_var();
            let r_var = state.fresh_type_var();
            state.promise_results.push((r_var.clone(), inner.clone()));
            let cb = state.callable_row_open(None, vec![err_var], r_var);
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
    /// Settle the `then` / `catch` callback results recorded since
    /// `mark` (see [`promise_method_type`]): a callback returning
    /// `Promise<V>` makes the call's promise a `Promise<V>`; one
    /// returning a plain `V`, a `Promise<V>` too. A result still unknown
    /// (and not a number) is taken to be a promise, as before callbacks
    /// could return values.
    pub(crate) fn settle_promise_results(
        &mut self,
        mark: usize,
        span: Span,
    ) -> Result<(), IntyError> {
        if self.promise_results.len() <= mark {
            return Ok(());
        }
        let pairs: Vec<(Type, Type)> = self.promise_results.drain(mark..).collect();
        for (r, u) in pairs {
            match self.zonk(&r) {
                Type::Promise(v) => self.unify(span, &u, &v)?,
                // Unknown: the conservative choice — a later non-promise
                // is a type error rather than a mistyped flattening.
                Type::Var(TVarName::Flex(_)) => self.unify(span, &r, &Type::promise(u))?,
                Type::Error => {}
                other => self.subsume(span, &other, &u)?,
            }
        }
        Ok(())
    }
}

impl InferState {
    /// Resolve pending type class constraints.
    /// This should be called after inference to check that all constraints are satisfiable.
    pub fn resolve_constraints(&mut self) -> Result<(), IntyError> {
        self.resolve_constraints_keeping(&Default::default())
    }

    /// [`Self::resolve_constraints`], except that the variables in `keep`
    /// aren't defaulted: an imported module's, which the bindings it
    /// leaves for its importers reach. Their uses there decide them, as
    /// in a single file.
    pub fn resolve_constraints_keeping(
        &mut self,
        keep: &std::collections::HashSet<TVarName>,
    ) -> Result<(), IntyError> {
        self.constraint_removals += 1;
        // Resolving one constraint can make another's container concrete
        // (an `Indexable` whose container is still a variable is deferred),
        // so iterate until nothing changes. Previously a single pass
        // dropped every constraint deferred this way, leaving its element
        // type unconstrained.
        let mut constraints = std::mem::take(&mut self.pending_constraints);
        loop {
            let before = constraints.len();
            let mut deferred = Vec::new();
            for constraint in constraints {
                if self.is_deferred(&constraint.pred) {
                    deferred.push(constraint);
                } else {
                    self.resolve_constraint(&constraint.pred, constraint.span)?;
                }
                // Resolving can pose new constraints (a property read
                // from a union's variable member).
                deferred.append(&mut self.pending_constraints);
            }
            if deferred.is_empty() {
                return Ok(());
            }
            if deferred.len() == before {
                // Nothing pinned down the receivers of the property reads
                // left: read them as fields of an object, as a direct
                // access to an object would. That's a valid choice for a
                // type nothing else constrains, and it can let the
                // `Indexable`s on the same receivers resolve.
                // Only the first read of each (receiver, name) becomes the
                // field: the receiver has no value, so further reads of
                // the name (`s.slice(i)`, `s.slice(i, j)`) are vacuous and
                // needn't agree.
                // (Keys are taken before any defaulting binds a receiver.)
                let keys: Vec<Option<(Type, String)>> = deferred
                    .iter()
                    .map(|c| {
                        c.pred
                            .as_has_prop()
                            .map(|(recv, name, _)| (self.zonk(recv), name.to_string()))
                    })
                    .collect();
                // A receiver that `+` also constrains is a number or a
                // string, never an object: its reads stay on the variable,
                // as the Lean model leaves them.
                let operands: Vec<Type> = deferred
                    .iter()
                    .filter(|c| c.pred.class == ClassName::Plus)
                    .flat_map(|c| c.pred.types.clone())
                    .collect();
                let operands: Vec<Type> = operands.iter().map(|t| self.zonk(t)).collect();
                let mut defaulted = false;
                let mut rest = Vec::new();
                let mut seen: Vec<(Type, String)> = Vec::new();
                for (c, key) in deferred.into_iter().zip(keys) {
                    match key {
                        // (Not one an importing module still sees, whose
                        // uses decide it: left here it would be dropped.)
                        Some(key)
                            if operands.contains(&key.0)
                                && !matches!(&key.0, Type::Var(v) if keep.contains(v)) =>
                        {
                            rest.push(c)
                        }
                        Some(key) => {
                            if !seen.contains(&key) {
                                seen.push(key);
                                self.default_has_prop(&c)?;
                            }
                            defaulted = true;
                        }
                        None => rest.push(c),
                    }
                }
                if !defaulted {
                    // Whatever is left has a container nothing ever pinned
                    // down: no use of it depends on the element type.
                    self.pending_constraints = rest;
                    // An `Inject` or a `Strip` on a variable an importing
                    // module still sees waits for its uses there (`put(true)`
                    // deciding what a cell's sum holds); dropped, they would
                    // let a value of no case through. (So does a `Spread`;
                    // one on a variable nothing will decide is dropped, as
                    // the Lean model leaves its `Merge`s: no value has a
                    // type nothing fixes, so no run reaches the spread.)
                    let pending = std::mem::take(&mut self.pending_constraints);
                    self.pending_constraints = pending
                        .into_iter()
                        .filter(|c| {
                            matches!(
                                c.pred.class,
                                ClassName::Inject | ClassName::Strip | ClassName::Spread
                            ) && matches!(
                                c.pred.types.first().map(|t| self.zonk(t)),
                                Some(Type::Var(v)) if keep.contains(&v)
                            )
                        })
                        .collect();
                    return Ok(());
                }
                constraints = rest;
                continue;
            }
            constraints = deferred;
        }
    }

    /// Resolve every pending `HasProp` whose receiver's type is now known
    /// (repeatedly: resolving one can pin down another's receiver). Run
    /// before generalising, so a function's scheme only keeps the
    /// property reads that really depend on its quantified variables,
    /// and after calls, so a result type is known as early as possible.
    pub(crate) fn simplify_has_props(&mut self) -> Result<(), IntyError> {
        self.constraint_removals += 1;
        loop {
            let ready: Vec<usize> = (0..self.pending_constraints.len())
                .filter(|&i| {
                    let pred = &self.pending_constraints[i].pred;
                    // (A `Plus` on a known type too: it is decided there,
                    // not carried in a scheme.)
                    matches!(
                        pred.class,
                        ClassName::HasProp
                            | ClassName::Indexable
                            | ClassName::Inject
                            | ClassName::Strip
                            | ClassName::Spread
                            | ClassName::Plus
                    ) && !self.is_deferred(pred)
                })
                .collect();
            if ready.is_empty() {
                return Ok(());
            }
            let mut taken = Vec::with_capacity(ready.len());
            for &i in ready.iter().rev() {
                taken.push(self.pending_constraints.remove(i));
            }
            for c in taken.into_iter().rev() {
                self.resolve_constraint(&c.pred, c.span)?;
            }
        }
    }

    /// Decide every pending `Plus` whose type is known by now, so a
    /// scheme carries only those on its variables.
    pub(crate) fn resolve_known_plus(&mut self) -> Result<(), IntyError> {
        let all = std::mem::take(&mut self.pending_constraints);
        let (known, rest): (Vec<_>, Vec<_>) = all
            .into_iter()
            .partition(|c| c.pred.class == ClassName::Plus && !self.is_deferred(&c.pred));
        self.pending_constraints = rest;
        for c in known {
            self.resolve_constraint(&c.pred, c.span)?;
        }
        Ok(())
    }

    /// Read `HasProp(receiver, name, result)` as a field of an object:
    /// bind the receiver to `{name: result | ρ}`. A valid choice for a
    /// receiver nothing else constrains (it only narrows the types the
    /// constraint admits), and what inty inferred before `HasProp`.
    fn default_has_prop(&mut self, c: &crate::infer::PendingConstraint) -> Result<(), IntyError> {
        let (recv, name, result) = c
            .pred
            .as_has_prop()
            .expect("default_has_prop: a HasProp constraint");
        let row = Type::object_open([(name, result.clone())], self.fresh_flex());
        self.unify(c.span, recv, &row)?;
        if let Some(this) = c.pred.method_this() {
            self.unify_this(c.span, this, recv)?;
        }
        Ok(())
    }

    /// A constraint that must wait for its first type (an `Indexable`'s
    /// container, a `HasProp`'s receiver, the type an `Inject` or a
    /// `Strip` relates to a sum, a `Plus`'s type) to be known.
    pub(crate) fn is_deferred(&self, pred: &TypePred) -> bool {
        matches!(
            pred.class,
            ClassName::Indexable
                | ClassName::HasProp
                | ClassName::Inject
                | ClassName::Strip
                | ClassName::Spread
                | ClassName::Plus
        ) && pred.types.first().is_some_and(|c| {
            // Only the head matters: follow the variable's bindings (a
            // whole substitution, applied to each pending constraint at
            // each call, was most of a large program's checking time).
            let mut head = c;
            for _ in 0..64 {
                match head {
                    Type::Var(v @ TVarName::Flex(_)) => match self.main_subst.get(v) {
                        Some(t) => head = t,
                        None => return true,
                    },
                    _ => return false,
                }
            }
            matches!(self.apply_subst(c), Type::Var(TVarName::Flex(_)))
        })
    }

    /// Resolve `HasProp(receiver, name, result)` for a known receiver:
    /// exactly what reading `.name` from a value of that type directly
    /// would have given — a string's or array's built-in property (a
    /// fresh copy of a method's type per read), an object's field.
    fn resolve_has_prop(
        &mut self,
        receiver: &Type,
        name: &str,
        result: &Type,
        this: Option<&Type>,
        span: Span,
    ) -> Result<(), IntyError> {
        let receiver = self.zonk(receiver);
        if matches!(receiver, Type::Var(TVarName::Flex(_))) {
            return Ok(());
        }
        if let Type::Union(members) = &receiver {
            // Every arm must give `result`. (A direct read from a union
            // joins the arms' fields into a union, but `result` may
            // already be pinned to one of them, and unify's `Union ~ T`
            // rule would accept that.) An arm whose type isn't known yet
            // gets its own constraint.
            for m in members {
                match self.zonk(m) {
                    m @ Type::Var(TVarName::Flex(_)) => {
                        self.add_constraint(TypePred::has_prop(m, name, result.clone()), span)
                    }
                    m => self.resolve_has_prop(&m, name, result, None, span)?,
                }
            }
            if let Some(this) = this {
                self.unify_this(span, this, &receiver)?;
            }
            return Ok(());
        }
        let promise_mark = self.promise_results.len();
        let found = match self.infer_member_on_type(&receiver, name, span) {
            Ok(t) => t,
            // A primitive without the property: say so, rather than
            // report the object shape it failed to unify with.
            Err(_)
                if matches!(
                    receiver,
                    Type::Number
                        | Type::Boolean
                        | Type::Null
                        | Type::Undefined
                        | Type::String
                        | Type::Literal(_)
                        | Type::Array(_)
                        | Type::Regex
                        | Type::TypedArray(_)
                ) =>
            {
                return Err(TypeError::PropertyNotFound {
                    prop: name.to_string(),
                    obj_type: self.show(&receiver),
                    span,
                }
                .into());
            }
            Err(e) => return Err(e),
        };
        match this {
            // A method call: check it as a direct call on this receiver
            // would be checked — each argument subsumed into its
            // parameter (`"\n"` into `String | Regex`), the result
            // unified — rather than equating the call's argument types
            // with the parameters.
            Some(this) => {
                self.apply_deferred_call(span, result, &found)?;
                let receiver = self.method_receiver(&receiver);
                self.unify_this(span, this, &receiver)?;
            }
            None => self.unify(span, result, &found)?,
        }
        // A deferred `p.then(cb)`: the call was checked already.
        self.settle_promise_results(promise_mark, span)?;
        Ok(())
    }

    /// Relate the call-site shape `site` (a callable whose parameters are
    /// the call's argument types) with the method `callee` it turned out
    /// to call, the way `infer_call` relates a known callee with its
    /// arguments.
    fn apply_deferred_call(
        &mut self,
        span: Span,
        site: &Type,
        callee: &Type,
    ) -> Result<(), IntyError> {
        use crate::infer::extract_callable;
        use crate::types::Presence;
        let (site_z, callee_z) = (self.zonk(site), self.zonk(callee));
        let (Some((_, args, site_ret)), Some((_, params, ret))) =
            (extract_callable(&site_z), extract_callable(&callee_z))
        else {
            // Not a function after all (or not yet known): relate the
            // types as they are, which reports the mismatch.
            return self.unify(span, site, callee);
        };
        for i in 0..args.len().max(params.len()) {
            match (args.get(i), params.get(i)) {
                (Some(a), Some(p)) => {
                    self.unify_presence(span, &a.presence, &p.presence)?;
                    // Subsumption matters where the parameter is a union or
                    // a `Number` (a number literal fits); elsewhere it is
                    // unification, done directly (no snapshot).
                    if matches!(
                        self.zonk(&p.ty),
                        Type::Union(_) | Type::Maybe(..) | Type::Number
                    ) {
                        self.subsume(span, &a.ty, &p.ty)?;
                    } else {
                        self.unify(span, &a.ty, &p.ty)?;
                    }
                }
                (Some(a), None) => self.unify_presence(span, &a.presence, &Presence::Abs)?,
                (None, Some(p)) => self.unify_presence(span, &p.presence, &Presence::Abs)?,
                (None, None) => unreachable!(),
            }
        }
        self.unify(span, &site_ret, &ret)
    }

    /// `record[key]`. A literal key selects that field (which must exist).
    /// Any other key is an error: a string known only at run time may name
    /// no field, and the read would give `undefined` where the type says
    /// otherwise. A string-keyed map is a `Dict<V>`, whose read gives
    /// `V | Undefined`.
    fn resolve_record_index(
        &mut self,
        container: &Type,
        literal_key: Option<String>,
        element: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        use crate::types::{PropName, RowTail, RowType};
        let Some(key) = literal_key else {
            return Err(TypeError::ConstraintNotSatisfied {
                class: "Indexable (a key known only at run time may name no field: \
                        use a literal key, or a `Dict<V>`)"
                    .to_string(),
                ty: self.show(container),
                span,
            }
            .into());
        };
        let rest = self.fresh_flex();
        let mut props = std::collections::BTreeMap::new();
        props.insert(PropName(key), self.read_entry(element.clone()));
        let wanted = Type::Row(RowType {
            props,
            tail: RowTail::Open(rest),
        });
        self.unify(span, container, &wanted)
    }

    /// Resolve a single type class constraint. An instance of a scheme's
    /// predicate (posed where a generic function is used) that fails says
    /// where the requirement is written too (`TypeError::RequiredBy`).
    fn resolve_constraint(&mut self, pred: &TypePred, span: Span) -> Result<(), IntyError> {
        self.resolve_constraint_here(pred, span)
            .map_err(|e| match (pred.origin, e) {
                (Some(origin), IntyError::Type(inner))
                    if origin != span && !matches!(*inner, TypeError::RequiredBy { .. }) =>
                {
                    TypeError::RequiredBy { inner, origin }.into()
                }
                (_, e) => e,
            })
    }

    fn resolve_constraint_here(&mut self, pred: &TypePred, span: Span) -> Result<(), IntyError> {
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
            ClassName::Plus => self.resolve_plus(&pred.types[0].clone(), span),
            ClassName::Indexable => {
                self.resolve_indexable(&pred.types[0], &pred.types[1], &pred.types[2], span)
            }
            ClassName::IndexWrite => self.resolve_index_write(&pred.types[0], span),
            ClassName::FieldWrite => {
                let (recv, name) = pred
                    .as_field_write()
                    .expect("FieldWrite predicates are built by TypePred::field_write");
                let (recv, name) = (recv.clone(), name.to_string());
                self.resolve_field_write(&recv, &name, span)
            }
            ClassName::HasProp => {
                let (recv, name, result) = pred
                    .as_has_prop()
                    .expect("HasProp predicates are built by TypePred::has_prop");
                let (recv, result) = (recv.clone(), result.clone());
                let this = pred.method_this().cloned();
                self.resolve_has_prop(&recv, name, &result, this.as_ref(), span)
            }
            // A known type: subsume it into the sum, which poses the
            // constraint again if the type is still a variable.
            ClassName::Inject => self.subsume(span, &pred.types[0], &pred.types[1]),
            ClassName::Strip => self.resolve_strip(&pred.types[0], &pred.types[1], span),
            ClassName::Spread => {
                self.resolve_spread(&pred.types[0], &pred.types[1], &pred.types[2], span)
            }
        }
    }

    /// Resolve `Strip τ σ`: a sum's value is its `σ`; nothing alone holds
    /// no value to strip down to (an error, as in the model, which has
    /// no instance for it); any other type is its own `σ`. Waits while
    /// `τ` is a variable.
    pub(crate) fn resolve_strip(
        &mut self,
        ty: &Type,
        sigma: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        match self.flatten_type(ty) {
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::strip(ty.clone(), sigma.clone()), span);
                Ok(())
            }
            Type::Maybe(_, inner) => self.unify(span, sigma, &inner),
            Type::Named(id, args) if !self.is_nominal_type(id) => {
                match self.unroll_named(id, &args) {
                    Some(unrolled) => self.resolve_strip(&unrolled, sigma, span),
                    None => self.unify(span, sigma, ty),
                }
            }
            t @ (Type::Null | Type::Undefined) => Err(TypeError::ConstraintNotSatisfied {
                class: "Strip (a value that is always nothing)".to_string(),
                ty: t.to_string(),
                span,
            }
            .into()),
            _ => self.unify(span, sigma, ty),
        }
    }

    /// Resolve `Plus a`: a number or a string has `+`, any other known
    /// type hasn't, and a variable waits.
    pub(crate) fn resolve_plus(&mut self, a: &Type, span: Span) -> Result<(), IntyError> {
        match self.zonk(a) {
            Type::Number
            | Type::String
            | Type::Literal(
                crate::types::LitValue::Number(_) | crate::types::LitValue::String(_),
            )
            | Type::Error => Ok(()),
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::plus(a.clone()), span);
                Ok(())
            }
            t => Err(TypeError::ConstraintNotSatisfied {
                class: "Plus".to_string(),
                ty: t.to_string(),
                span,
            }
            .into()),
        }
    }

    /// Resolve `IndexWrite c`: an element of any indexable container can be
    /// stored but a string's; a variable nothing pinned down holds no
    /// value, so its stores never run.
    pub(crate) fn resolve_index_write(
        &mut self,
        container: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        match self.apply_subst(container) {
            Type::String | Type::Literal(crate::types::LitValue::String(_)) => {
                Err(TypeError::ConstraintNotSatisfied {
                    class: "IndexWrite (a string's characters can't be assigned)".to_string(),
                    ty: "String".to_string(),
                    span,
                }
                .into())
            }
            _ => Ok(()),
        }
    }

    /// Resolve `FieldWrite r "p"`: an object's property that takes stores
    /// can be stored (not a getter, nor a class's method), not a built-in
    /// one of an array, a string or a function (which `dynamics` doesn't
    /// store, and a string's a strict program can't); a variable nothing
    /// pinned down holds no value.
    pub(crate) fn resolve_field_write(
        &mut self,
        receiver: &Type,
        name: &str,
        span: Span,
    ) -> Result<(), IntyError> {
        let receiver = self.apply_subst(receiver);
        // An array's `length` takes a store (`xs.length = 0` empties it in
        // place); the number stored is checked as the property's type.
        if name == "length" && matches!(receiver, Type::Array(_)) {
            return Ok(());
        }
        let builtin = match &receiver {
            // A function's row has a call signature; one a spread's result
            // carries as absent (`{...{...o}}`) is an object's.
            Type::Row(row) => row.props.iter().any(|(k, e)| {
                k.0 == crate::types::CALLABLE_KEY
                    && !matches!(
                        self.main_subst.resolve_presence(&e.presence),
                        crate::types::Presence::Abs
                    )
            }),
            Type::Var(_) | Type::Named(..) | Type::Error => false,
            _ => true,
        };
        if builtin {
            return Err(TypeError::ConstraintNotSatisfied {
                class: "FieldWrite (only an object's properties can be assigned)".to_string(),
                ty: self.show(&receiver),
                span,
            }
            .into());
        }
        if matches!(receiver, Type::Var(_) | Type::Error) {
            return Ok(());
        }
        // The property takes stores: unify the receiver with a row whose
        // property does.
        let ty = self.fresh_type_var();
        let entry = self.write_entry(ty);
        let rest = self.fresh_flex();
        let wanted = Type::Row(crate::types::RowType::open_entries(
            std::collections::BTreeMap::from([(crate::types::PropName(name.to_string()), entry)]),
            rest,
        ));
        self.unify(span, &receiver, &wanted)
    }

    /// The receiver of an assignment's member target must take the store
    /// to `name` (`FieldWrite`): decided now for a known type, posed for a
    /// variable.
    pub(crate) fn require_field_write(
        &mut self,
        receiver: &Type,
        name: &str,
        span: Span,
    ) -> Result<(), IntyError> {
        match self.apply_subst(receiver) {
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::field_write(receiver.clone(), name), span);
                Ok(())
            }
            _ => self.resolve_field_write(receiver, name, span),
        }
    }

    /// The container of an assignment's computed-member target must take
    /// stores (`IndexWrite`): decided now for a known type, posed for a
    /// variable.
    pub(crate) fn require_index_write(
        &mut self,
        container: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        match self.apply_subst(container) {
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::index_write(container.clone()), span);
                Ok(())
            }
            _ => self.resolve_index_write(container, span),
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
        // A literal index (`xs[0]`) carries its singleton type; the
        // container's key type is the base type, as in the eager rule in
        // `infer_computed_member` (which subsumes rather than unifies).
        // The literal itself still selects a record field (`o["x"]`).
        let literal_key = match self.apply_subst(index) {
            Type::Literal(crate::types::LitValue::String(k)) => Some(k),
            _ => None,
        };
        let raw_index = self.apply_subst(index);
        let index = raw_index.widen_fresh_literals();
        let element = self.apply_subst(element);
        // An array or string index is a number (one with a fractional
        // part, or out of range, reads nothing: a fault).
        let int_index = |state: &mut Self| -> Result<(), IntyError> {
            match &raw_index {
                lit @ Type::Literal(_) => state.subsume(span, lit, &Type::Number),
                other => state.unify(span, other, &Type::Number),
            }
        };

        match &container {
            // Array indexing: [T][Number] = T
            Type::Array(elem_ty) => {
                int_index(self)?;
                self.unify(span, &element, elem_ty)?;
                Ok(())
            }

            // String indexing: String[Number] = String (a string literal's
            // too: `"xyz"[0]`)
            Type::String | Type::Literal(crate::types::LitValue::String(_)) => {
                int_index(self)?;
                self.unify(span, &element, &Type::String)?;
                Ok(())
            }

            Type::TypedArray(kind) => {
                int_index(self)?;
                self.unify(span, &element, &kind.element())?;
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
                        int_index(self)?;
                        self.unify(span, &element, &elem_var)?;
                        return Ok(());
                    }
                }

                // Object indexing with a string key.
                self.unify(span, &index, &Type::String)?;
                self.resolve_record_index(&container, literal_key, &element, span)
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
    fn test_resolve_plus_number_and_string() {
        let mut state = InferState::new();
        assert!(state.resolve_plus(&Type::Number, Span::new(0, 0)).is_ok());
        assert!(state.resolve_plus(&Type::String, Span::new(0, 0)).is_ok());
    }

    #[test]
    fn test_resolve_plus_other_is_an_error() {
        let mut state = InferState::new();
        assert!(state.resolve_plus(&Type::Boolean, Span::new(0, 0)).is_err());
    }

    #[test]
    fn test_resolve_plus_variable() {
        let mut state = InferState::new();
        let a = Type::flex(0);
        assert!(state.resolve_plus(&a, Span::new(0, 0)).is_ok());
        // Type variables are kept (not defaulted) to preserve polymorphism
        assert_eq!(state.apply_subst(&a), a);
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

        // The index should be a number (array-style), not a string
        // (object-style)
        assert_eq!(state.apply_subst(&index), Type::Number);
    }

    #[test]
    fn test_resolve_indexable_object_row() {
        let mut state = InferState::new();
        // {foo: String, bar: Number} is not array-like: a string key reads
        // a field, the one a literal key names.
        let row = Type::object([("foo", Type::String), ("bar", Type::Number)]);
        let key = Type::Literal(crate::types::LitValue::String("bar".into()));
        let elem = Type::flex(1);
        assert!(state
            .resolve_indexable(&row, &key, &elem, Span::new(0, 0))
            .is_ok());
        assert_eq!(state.apply_subst(&elem), Type::Number);

        // A key known only at run time may name no field.
        let index = Type::flex(0);
        assert!(state
            .resolve_indexable(&row, &index, &Type::flex(2), Span::new(0, 0))
            .is_err());
    }
}
