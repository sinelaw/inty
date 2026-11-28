//! Built-in types and type class constraint resolution.
//!
//! This module provides:
//! - Initial type environment with built-in functions
//! - Type class instances for Plus and Indexable
//! - Constraint solving for deferred type class predicates

use crate::error::{IntyError, TypeError};
use crate::infer::{InferState, TypeEnv};
use crate::span::Span;
use crate::types::{ClassName, Presence, PropName, RowType, TVarName, Type, TypePred, TypeScheme};

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
        // Regex form for HTML scrubbing. The replacement is a string or a
        // function of the match. JavaScript passes the function more —
        // the capture groups (each a string, or `undefined` when it
        // didn't take part), then the offset (a number) and the whole
        // string — whose types depend on the pattern; only the match,
        // always a string, is modelled, so a replacer takes one
        // parameter.
        "replace" | "replaceAll" => Type::simple_func(
            vec![
                Type::union(vec![s.clone(), Type::Regex]),
                Type::union(vec![
                    s.clone(),
                    Type::simple_func(vec![s.clone()], s.clone()),
                ]),
            ],
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
    let starlark = state.language == crate::ast::SourceLanguage::Starlark;
    // Starlark's strings have fewer methods than Python's, and one of their
    // own (`elems`); a Python-only method doesn't exist on them.
    if starlark && !STARLARK_STRING_METHODS.contains(&method) {
        return None;
    }
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
        // `s.partition(sep)` → (before, sep, after); `rpartition` splits at
        // the last `sep`.
        "partition" | "rpartition" => Type::simple_func(
            vec![s.clone()],
            Type::Tuple(vec![s.clone(), s.clone(), s.clone()]),
        ),
        // Starlark: `s.elems()`, the one-character strings of `s` (a
        // string itself isn't iterable). Modelled as a list of them,
        // which is what the elements are iterated and indexed as.
        "elems" if starlark => Type::simple_func(vec![], Type::array(s.clone())),
        // `s[a:b:c]`, lowered by the parser to a call of `SLICE_METHOD`.
        crate::frontends::python::SLICE_METHOD => slice_method(s.clone()),
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
        | "isnumeric" | "isdecimal" | "isidentifier" | "isprintable" | "isascii" => {
            Type::simple_func(vec![], b.clone())
        }
        _ => {
            let _ = (state, n, s, b);
            return None;
        }
    })
}

/// Look up a built-in Regex prototype method by name. Each call gets a
/// fresh function type. `test` returns Boolean; `exec` returns the whole
/// match and the capture groups, or `null` when nothing matches, as
/// `String.prototype.match` does.
pub fn regex_method_type(state: &mut InferState, method: &str) -> Option<Type> {
    let _ = state;
    let s = Type::String;
    let n = Type::Number;
    let b = Type::Boolean;
    Some(match method {
        "test" => Type::simple_func(vec![s.clone()], b.clone()),
        "exec" => Type::simple_func(
            vec![s.clone()],
            Type::union(vec![Type::array(s.clone()), Type::Null]),
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
        "BYTES_PER_ELEMENT" => Type::Number,
        "buffer" => array_buffer_type(state)?,
        _ => return None,
    })
}

/// The stdlib's `ArrayBuffer` type (`None` without the stdlib).
pub fn array_buffer_type(state: &InferState) -> Option<Type> {
    let def = state.type_aliases.get("ArrayBuffer")?;
    Some(match def.rec_id {
        Some(id) => Type::Named(id, Vec::new()),
        None => def.body.clone(),
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
    // `Array.prototype.flat()`: an array of arrays made one array. Its
    // receiver says the elements are arrays (`U[][]`), as `this:` would
    // in a declaration. A depth (`flat(2)`) isn't taken: the result's
    // type would depend on the number, and a non-array element (which
    // `flat` keeps) isn't one, so mixed nesting is rejected, never
    // mistyped.
    if method == "flat" {
        let u = state.fresh_type_var();
        return Some(with_receiver(
            Type::simple_func(vec![], Type::array(u.clone())),
            Type::array(Type::array(u)),
        ));
    }
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
        // `pop()` / `shift()`: the removed element, or `undefined` when
        // the array is empty.
        "pop" => Type::simple_func(vec![], Type::union(vec![elem.clone(), u.clone()])),
        "shift" => Type::simple_func(vec![], Type::union(vec![elem.clone(), u.clone()])),
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
        // `flatMap(f)`: each element's array of a fresh element type U,
        // joined into one. (JavaScript also takes a non-array result as
        // a single element; here the callback gives an array.)
        "flatMap" => {
            let u_var = state.fresh_type_var();
            let cb = element_callback(state, elem, Type::array(u_var.clone()));
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

/// The type of the method a slice subscript lowers to: three
/// bounds, each a number or `None` (omitted), giving a value of the
/// receiver's own type `of`.
fn slice_method(of: Type) -> Type {
    let bound = Type::union([Type::Number, Type::Null]);
    Type::simple_func(vec![bound.clone(), bound.clone(), bound], of)
}

/// The `str` methods of the Starlark specification (and Bazel), plus the
/// slice method a slice subscript lowers to. The others in
/// [`python_string_method_type`] are Python's only.
const STARLARK_STRING_METHODS: &[&str] = &[
    "capitalize",
    "count",
    "elems",
    "endswith",
    "find",
    "format",
    "index",
    "isalnum",
    "isalpha",
    "isdigit",
    "islower",
    "isspace",
    "istitle",
    "isupper",
    "join",
    "lower",
    "lstrip",
    "partition",
    "removeprefix",
    "removesuffix",
    "replace",
    "rfind",
    "rindex",
    "rpartition",
    "rsplit",
    "rstrip",
    "split",
    "splitlines",
    "startswith",
    "strip",
    "title",
    "upper",
    crate::frontends::python::SLICE_METHOD,
];

/// The `list` methods of the Starlark specification (and Bazel), plus the
/// slice method. Python's `count`, `sort`, `reverse` and `copy` aren't
/// among them.
const STARLARK_LIST_METHODS: &[&str] = &[
    "append",
    "clear",
    "extend",
    "index",
    "insert",
    "pop",
    "remove",
    crate::frontends::python::SLICE_METHOD,
];

/// Look up a Python `dict` method by name, for a `Dict` (`dict[str, V]`)
/// whose values are `value`. The keys are strings, as a `Dict`'s are.
/// Mutators return `None` (the language unit `Null`).
///
/// `keys()`, `values()` and `items()` are modelled as lists: they are in
/// Starlark, and in Python they are views that iterate the same way (a
/// view can't be indexed, which a list can).
pub fn python_dict_method_type(state: &mut InferState, value: &Type, method: &str) -> Option<Type> {
    use crate::types::FuncParam;
    if state.language == crate::ast::SourceLanguage::Starlark && method == "copy" {
        return None;
    }
    let s = Type::String;
    let nil = Type::Null;
    let entry = Type::Tuple(vec![s.clone(), value.clone()]);
    Some(match method {
        // `d.get(k, default?)`: the value, or `None` for a missing key. A
        // call that gives a default the receiver is known to be a `Dict`
        // for gets a tighter type at the call ([`dict_get_with_default`]).
        "get" => {
            let pvar = state.fresh_pvar();
            let maybe = Type::union([value.clone(), nil.clone()]);
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(s.clone()),
                    FuncParam::optional(pvar, maybe.clone()),
                ],
                maybe,
            )
        }
        "keys" => Type::simple_func(vec![], Type::array(s.clone())),
        "values" => Type::simple_func(vec![], Type::array(value.clone())),
        "items" => Type::simple_func(vec![], Type::array(entry.clone())),
        // `d.pop(k, default?)`: the value (a missing key without a default
        // raises).
        "pop" => {
            let pvar = state.fresh_pvar();
            Type::simple_func_with_params(
                vec![
                    FuncParam::required(s.clone()),
                    FuncParam::optional(pvar, value.clone()),
                ],
                value.clone(),
            )
        }
        "popitem" => Type::simple_func(vec![], entry),
        "setdefault" => Type::simple_func(vec![s.clone(), value.clone()], value.clone()),
        "update" => Type::simple_func(vec![Type::map(value.clone())], nil.clone()),
        "clear" => Type::simple_func(vec![], nil.clone()),
        "copy" => Type::simple_func(vec![], Type::map(value.clone())),
        _ => return None,
    })
}

/// The type of `d.get(k, default)` when `d` is known to be a `Dict` with
/// values `value` and the default isn't `None`: the value, never `None`
/// (the default stands in for a missing key, and must be a value).
pub fn dict_get_with_default(value: &Type) -> Type {
    Type::simple_func(vec![Type::String, value.clone()], value.clone())
}

/// Look up a Python `list` method by name for a list whose element type
/// is `elem`. Separate from the JavaScript [`array_method_type`] surface
/// (issue #67); inference picks the table by `Program::language`. In-place
/// mutators return `None` (modelled as the language unit `Null`).
pub fn python_list_method_type(state: &mut InferState, elem: &Type, method: &str) -> Option<Type> {
    use crate::types::FuncParam;
    // Starlark's lists have only some of Python's methods.
    if state.language == crate::ast::SourceLanguage::Starlark
        && !STARLARK_LIST_METHODS.contains(&method)
    {
        return None;
    }
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
        // `xs[a:b:c]`, lowered by the parser to a call of `SLICE_METHOD`.
        crate::frontends::python::SLICE_METHOD => slice_method(arr.clone()),
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
            match self.zonk_head(&r) {
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
    /// Its error is rendered (`render_error`).
    pub fn resolve_constraints_keeping(
        &mut self,
        keep: &std::collections::HashSet<TVarName>,
    ) -> Result<(), IntyError> {
        self.resolve_constraints_unrendered(keep)
            .map_err(|e| self.render_error(e))
    }

    fn resolve_constraints_unrendered(
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
                // field, of a receiver nothing after this module sees: it
                // has no value, so further reads of the name (`s.slice(i)`,
                // `s.slice(i, j)`) are vacuous and needn't agree. One an
                // importing module sees has the importer's values: each
                // read is of the field.
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
                let operands: Vec<Type> = operands.iter().map(|t| self.zonk_head(t)).collect();
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
                        // A receiver an importing module still sees has the
                        // importer's values: its reads wait for them, each
                        // resolved against the value's type (an array's
                        // `map`, read twice, instantiated for each). Made
                        // the first read's field, a record, every other
                        // read's requirement was lost (a `.toUpperCase()` on
                        // what it gives), and an array or a string given
                        // didn't fit.
                        Some(key) if matches!(&key.0, Type::Var(v) if keep.contains(v)) => {
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
                    // Whatever is left on a variable nothing will decide has
                    // a container nothing ever pinned down: no use of it
                    // depends on the element type, and no value has a type
                    // nothing fixes (so no run reaches a `Spread` on it, as
                    // the Lean model leaves its `Merge`s): it is dropped.
                    // One on a variable an importing module still sees,
                    // whatever its class, waits for its uses there (an
                    // `Inject`: `put(true)` deciding what a cell's sum
                    // holds; an `Iterable` or `Indexable`: what the
                    // importer's array holds, iterated): dropped, the
                    // importer's value was never checked against it.
                    self.pending_constraints = rest;
                    let pending = std::mem::take(&mut self.pending_constraints);
                    self.pending_constraints = pending
                        .into_iter()
                        .filter(|c| {
                            matches!(
                                c.pred.types.first().map(|t| self.zonk_head(t)),
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
                            | ClassName::Iterable
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
    ///
    /// A method call's (`recv.name(…)`) callee is called on the receiver.
    /// Where an importing module still decides the receiver (`kept`), it
    /// also decides the callee: a function that uses no `this` is called
    /// on any receiver as well as detached, so the callee's `this` waits
    /// as an unknown callee's does (`settle_receivers`, at the end of the
    /// importer) rather than making it a method of the receiver now.
    fn default_has_prop(&mut self, c: &crate::infer::PendingConstraint) -> Result<(), IntyError> {
        let (recv, name, result) = c
            .pred
            .as_has_prop()
            .expect("default_has_prop: a HasProp constraint");
        let tail = self.fresh_flex();
        self.note_field_read(&tail, name, result);
        // A field as a read leaves it (`read_entry`): whether it takes
        // stores, and is the object's own, are for its other uses to say.
        // (An assignable own field, a class's method or getter given for
        // the receiver later didn't fit: `v.setTop(0, 0)` on the elements
        // of an array an importer fills with views.)
        let entry = self.read_entry(result.clone());
        let row = Type::Row(crate::types::RowType::open_entries(
            std::collections::BTreeMap::from([(crate::types::PropName(name.to_string()), entry)]),
            tail,
        ));
        self.unify(c.span, recv, &row)?;
        if let Some(this) = c.pred.method_this() {
            self.unify_this(c.span, this, recv)?;
        }
        Ok(())
    }

    /// A read's type not fitting the field it reads, said as a mismatch
    /// at that member of the receiver (the record the read asks for, and
    /// the receiver), with where each side came from: a read resolved
    /// late (the receiver an importer's value) is reported as a direct
    /// one is.
    fn as_member_mismatch(
        &mut self,
        e: &mut IntyError,
        name: &str,
        result: &Type,
        receiver: &Type,
    ) {
        use crate::error::ShownType;
        let tail = self.fresh_flex();
        self.note_field_read(&tail, name, result);
        let asked = Type::object_open([(name, result.clone())], tail);
        // Where the receiver's field came from (an object literal's, kept
        // on the field's type as it was written).
        let field_origin = match self.zonk_head(receiver) {
            Type::Row(row) => row
                .props
                .get(&crate::types::PropName(name.to_string()))
                .and_then(|f| self.get_origin(&f.ty).cloned()),
            _ => None,
        };
        if let Some(TypeError::UnificationError {
            member,
            whole,
            found_origin,
            ..
        }) = e.as_type_mut()
        {
            if member.is_none() {
                *member = Some(name.to_string());
                *whole = Some(Box::new((ShownType::ty(&asked), ShownType::ty(receiver))));
                if found_origin.is_none() {
                    *found_origin = field_origin;
                }
                self.settle_error(e);
            }
        }
    }

    /// A constraint that must wait for its first type (an `Indexable`'s
    /// container, a `HasProp`'s receiver, the type an `Inject` or a
    /// `Strip` relates to a sum, a `Plus`'s type) to be known.
    pub(crate) fn is_deferred(&self, pred: &TypePred) -> bool {
        matches!(
            pred.class,
            ClassName::Indexable
                | ClassName::Iterable
                | ClassName::HasProp
                | ClassName::Inject
                | ClassName::Strip
                | ClassName::Spread
                | ClassName::Plus
                // A store, or a test, on a variable waits for it too:
                // resolved on one, it said nothing and was gone, and a
                // value an importer gives later wasn't checked.
                | ClassName::FieldWrite
                | ClassName::IndexWrite
                | ClassName::Testable
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
        let receiver = self.zonk_head(receiver);
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
                match self.zonk_head(m) {
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
                // The method's own `this` is the receiver too, as in a
                // direct call (`apply_deferred_call` relates the
                // arguments and the result): a method of another object,
                // reading its `this` (`new K().say`), doesn't fit.
                let callee = self.zonk_head(&found);
                if let Some((Some(callee_this), _, _)) = crate::infer::extract_callable(&callee) {
                    self.unify_this(span, &callee_this, &receiver)?;
                }
            }
            None => {
                if let Err(mut e) = self.unify(span, result, &found) {
                    self.as_member_mismatch(&mut e, name, result, &receiver);
                    return Err(e);
                }
            }
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
        let (site_z, callee_z) = (self.zonk_head(site), self.zonk_head(callee));
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
                        self.zonk_head(&p.ty),
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
            props: props.into(),
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
        // What the constraint would have found out about a value of an
        // `Error` type (an element, a field) is `Error` too: left a free
        // variable, its first use would pin it (`const c = bad[i];
        // c && c.f !== ""` made `c` a `Boolean`).
        if let Some(first) = pred.types.first() {
            if matches!(self.zonk_head(first), Type::Error) {
                for t in &pred.types[1..] {
                    self.absorb_error(span, t);
                }
                return Ok(());
            }
        }
        if pred
            .types
            .iter()
            .any(|t| matches!(self.zonk_head(t), Type::Error))
        {
            return Ok(());
        }
        match pred.class {
            ClassName::Plus => self.resolve_plus(&pred.types[0].clone(), span),
            ClassName::Indexable => {
                self.resolve_indexable(&pred.types[0], &pred.types[1], &pred.types[2], span)
            }
            ClassName::IndexWrite => self.resolve_index_write(&pred.types[0], span),
            ClassName::Testable => self.resolve_testable(&pred.types[0], span),
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
            ClassName::Iterable => self.resolve_iterable(&pred.types[0], &pred.types[1], span),
        }
    }

    /// `container` is iterated (`for … of`, a spread, `Array.from`): its
    /// element type is `element`. Decided now for a known container,
    /// posed (`Iterable`) for a variable.
    pub(crate) fn require_iterable(
        &mut self,
        container: &Type,
        element: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        self.resolve_iterable(container, element, span)
    }

    /// Whether the record `container` takes a `[Symbol.iterator]: element`
    /// field, as a read of it would add (see `resolve_iterable`): if it
    /// does, it now has it; if not, nothing changed.
    fn iterate_as_read(&mut self, container: &Type, element: &Type, span: Span) -> bool {
        let entry = self.read_entry(element.clone());
        let tail = self.fresh_flex();
        let read = Type::Row(RowType::open_entries(
            std::collections::BTreeMap::from([(
                PropName(crate::types::ITER_KEY.to_string()),
                entry,
            )]),
            tail,
        ));
        let snap = self.snapshot_inference();
        if self.quietly(|s| s.unify(span, &read, container)).is_ok() {
            return true;
        }
        self.restore_snapshot(snap);
        false
    }

    /// Resolve `Iterable c e` (see [`ClassName::Iterable`]).
    pub(crate) fn resolve_iterable(
        &mut self,
        container: &Type,
        element: &Type,
        span: Span,
    ) -> Result<(), IntyError> {
        let not_iterable = |s: &mut Self, why: &str| -> Result<(), IntyError> {
            Err(TypeError::ConstraintNotSatisfied {
                class: format!("Iterable ({why})"),
                ty: s.show(container),
                span,
            }
            .into())
        };
        match self.zonk_head(container) {
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::iterable(container.clone(), element.clone()), span);
                Ok(())
            }
            Type::Error => Ok(()),
            Type::Array(elem) => self.unify(span, element, &elem),
            Type::String | Type::Literal(crate::types::LitValue::String(_))
                if self.language == crate::ast::SourceLanguage::Starlark =>
            {
                not_iterable(
                    self,
                    "a Starlark string isn't iterable: iterate `s.elems()` for its \
                     one-character strings",
                )
            }
            Type::String | Type::Literal(crate::types::LitValue::String(_)) => {
                self.unify(span, element, &Type::String)
            }
            Type::TypedArray(_) => self.unify(span, element, &Type::Number),
            Type::Tuple(components) => {
                for c in &components {
                    self.unify(span, element, c)?;
                }
                Ok(())
            }
            Type::Union(members) => {
                for m in &members {
                    self.resolve_iterable(m, element, span)?;
                }
                Ok(())
            }
            Type::Named(id, args) => match self.unroll_named(id, &args) {
                Some(unrolled) => self.resolve_iterable(&unrolled, element, span),
                None => not_iterable(self, "not an iterable type"),
            },
            Type::Row(_) => match self.row_field_entry(container, crate::types::ITER_KEY) {
                Some(entry) if self.main_subst.resolve_presence(&entry.presence).is_pre() => {
                    self.unify(span, element, &entry.ty)
                }
                // A record of the fields a value's uses read (an object
                // not known yet, `xs.find(…)` on a value of unknown type):
                // iterating it reads its `[Symbol.iterator]`, as a read of
                // `find` does. Whether the value has one is decided where
                // its type is (an array has; a record that may not, or a
                // closed one without it, can't take it, and isn't
                // iterable).
                _ if self.iterate_as_read(container, element, span) => Ok(()),
                _ if self.row_field_entry(container, "length").is_some() => not_iterable(
                    self,
                    "an array-like object (`{length: n}`) isn't iterable; \
                     `Array.from(o, (_, i) => …)` maps its indices",
                ),
                _ => not_iterable(
                    self,
                    "an object isn't iterable unless its type says what it gives, \
                     `[Symbol.iterator]: T`; iterate `Object.keys(o)`, `Object.values(o)` or \
                     `Object.entries(o)`",
                ),
            },
            // Python and Starlark iterate a dict's keys.
            Type::Map(_) if self.language.is_python_like() => {
                self.unify(span, element, &Type::String)
            }
            Type::Map(_) => not_iterable(
                self,
                "a `Dict` is a plain object: iterate `Object.keys(d)`, `Object.values(d)` or \
                 `Object.entries(d)`",
            ),
            Type::Maybe(..) => not_iterable(self, "it may be `null` or `undefined`: test it first"),
            _ => not_iterable(
                self,
                "`for … of`, a spread and `Array.from` take an array, a string, a `Set`, a `Map` \
                 or another iterable",
            ),
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
        match self.zonk_head(ty) {
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
        match self.zonk_head(a) {
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
        match self.zonk_head(container) {
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
        // Only its head decides (see `resolve_testable`).
        let receiver = self.zonk_head(receiver);
        // An array's `length` takes a store (`xs.length = 0` empties it in
        // place); the number stored is checked as the property's type.
        if name == "length" && matches!(receiver, Type::Array(_)) {
            return Ok(());
        }
        // A regex's `lastIndex` takes a store too: it is where the next
        // `exec`/`test` of a global or sticky regex starts (`re.lastIndex = 0`
        // rewinds it); the number stored is checked as the property's type.
        if name == "lastIndex" && matches!(receiver, Type::Regex) {
            return Ok(());
        }
        // `d.key = v` on a JavaScript `Dict<V>` stores that key, as
        // `d["key"] = v` does.
        if matches!(receiver, Type::Map(_))
            && self.language == crate::ast::SourceLanguage::JavaScript
        {
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
        match self.zonk_head(receiver) {
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::field_write(receiver.clone(), name), span);
                Ok(())
            }
            _ => self.resolve_field_write(receiver, name, span),
        }
    }

    /// Resolve `Testable τ`: a value of `τ` may be tested for truthiness
    /// but a function or a promise, which are always truthy, and but a
    /// value of an annotation's type parameter (a skolem), which may stand
    /// for a function. A caught exception may be anything and is tested
    /// like the model's `unknown`; a variable nothing pinned down holds no
    /// value, so its tests never run.
    pub(crate) fn resolve_testable(&mut self, ty: &Type, span: Span) -> Result<(), IntyError> {
        // Only its head decides (and a row's call signature): resolving
        // it whole would write out a large type (an element's) as a tree.
        let original = ty;
        let ty = self.zonk_head(ty);
        // A row may carry a call signature whose presence isn't decided
        // yet (a spread of an operand not known yet): it waits, as on a
        // variable.
        let call = match &ty {
            Type::Func { .. } => Some(Presence::Pre),
            Type::Row(row) => row
                .props
                .get(&PropName(crate::types::CALLABLE_KEY.to_string()))
                .map(|entry| self.main_subst.resolve_presence(&entry.presence)),
            _ => None,
        };
        if let Some(Presence::Var(_)) = call {
            self.add_constraint(TypePred::testable(original.clone()), span);
            return Ok(());
        }
        let why = match &ty {
            Type::Promise(_) => {
                "a promise is always truthy, so this test always comes out the same: `await` it"
            }
            _ if call == Some(Presence::Pre) => {
                "a function is always truthy, so this test always comes out the same: call it"
            }
            Type::Var(TVarName::Skolem(id)) if !self.caught_exceptions.contains(id) => {
                "a type parameter may stand for a function, which is always truthy"
            }
            _ => return Ok(()),
        };
        Err(TypeError::ConstraintNotSatisfied {
            class: format!("Testable ({why})"),
            ty: self.show(original),
            span,
        }
        .into())
    }

    /// A value is tested for truthiness (`Testable`): decided now for a
    /// known type, posed for a variable.
    pub(crate) fn require_testable(&mut self, ty: &Type, span: Span) -> Result<(), IntyError> {
        match self.zonk_head(ty) {
            Type::Var(TVarName::Flex(_)) => {
                self.add_constraint(TypePred::testable(ty.clone()), span);
                Ok(())
            }
            _ => self.resolve_testable(ty, span),
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
        match self.zonk_head(container) {
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
        // Its head decides which container it is (see `resolve_testable`).
        let container = self.zonk_head(container);
        // A literal index (`xs[0]`) carries its singleton type; the
        // container's key type is the base type, as in the eager rule in
        // `infer_computed_member` (which subsumes rather than unifies).
        // The literal itself still selects a record field (`o["x"]`).
        let literal_key = match self.zonk_head(index) {
            Type::Literal(crate::types::LitValue::String(k)) => Some(k),
            _ => None,
        };
        let raw_index = self.zonk_head(index);
        let index = raw_index.widen_fresh_literals();
        let element = element.clone();
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

            // Tuple indexing, as the eager rule (`infer_computed_member`):
            // a constant index reads its component (one out of range
            // reads nothing), any other the union of the components.
            Type::Tuple(elems) => {
                int_index(self)?;
                if let Type::Literal(crate::types::LitValue::Number(n)) = &raw_index {
                    if n.fract() == 0.0 && *n >= 0.0 && (*n as usize) < elems.len() {
                        return self.unify(span, &element, &elems[*n as usize]);
                    }
                    return Err(TypeError::PropertyNotFound {
                        prop: n.to_string(),
                        obj_type: container.to_string(),
                        span,
                    }
                    .into());
                }
                self.unify(span, &element, &Type::union(elems.clone()))
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

    /// A read left at a module's end, on a receiver no importer sees, is
    /// made a field as a read needs it: present, of any kind. A class's
    /// method or a getter the receiver is found to be afterwards (as the
    /// rest of the module's constraints resolve) fits it; an own field
    /// that takes stores, as a store would need, it wouldn't.
    #[test]
    fn a_read_left_at_a_modules_end_takes_a_classs_method() {
        let mut state = InferState::new();
        let v = state.fresh_flex();
        let r = state.fresh_type_var();
        state.add_constraint(
            TypePred::has_prop(Type::Var(v.clone()), "setTop", r),
            Span::new(0, 0),
        );
        state
            .resolve_constraints_keeping(&std::collections::HashSet::new())
            .expect("the read is defaulted");
        let method = Type::Row(crate::types::RowType::closed_entries(
            std::collections::BTreeMap::from([(
                crate::types::PropName("setTop".to_string()),
                crate::types::FieldEntry {
                    presence: Presence::Pre,
                    ty: Type::Number,
                    writable: Presence::Abs,
                    own: Presence::Abs,
                },
            )]),
        ));
        assert!(
            state.unify(Span::new(0, 0), &Type::Var(v), &method).is_ok(),
            "a class's method fits the read"
        );
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
