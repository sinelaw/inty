# minfern

Type checker with full type inference for a subset of JavaScript.

Try it online at: https://sinelaw.github.io/minfern/

Based on the type system developed for [infernu](https://github.com/sinelaw/infernu). See [infernu.md](infernu.md) for a partial formalization. The implementation also covers `this` resolution, Rank-1 restrictions on type annotations, and a value restriction for generalisation and polymorphic-property mutation; the formal document doesn't go into these.

The JavaScript checked by minfern is just JavaScript and can be run by browsers or any other runtime, or even embedded engines. See [mquickjs](https://github.com/bellard/mquickjs) which is a runtime that also supports a subset of JavaScript.

## Strict by Design

minfern isn't a strict mode you opt into — it's the only mode. Every variable, expression, and function return has a single type for its lifetime. The type may be polymorphic, or a closed union of literals or row shapes, but it can't *change* under assignment, and operators that combine values still require their operands' types to agree. The benefit is that type errors in JavaScript become compile-time errors, with no runtime fallback.

## Type System Features

### Full Type Inference

No annotations required — every type is inferred. Annotations are accepted (in JSDoc comments or inline) for documentation; minfern can also emit them for you.

```javascript
function add(x, y) { return x + y; }
var n = add(1, 2);
```

Inferred:

```
function add<a> where Plus a => (a, a) => a
var n: Number
```

The function is polymorphic in any type that supports `+` (the `Plus` type class — see below). The call site instantiates it at `Number`.

### Parametric Polymorphism (Generic Functions)

`function id(x) { return x; }` works with any type. minfern infers `id<a>(a) => a`:

```javascript
function id(x) { return x; }
var a = id(42);
var b = id("hello");
```

```
function id<a>(a) => a
var a: Number
var b: String
```

### Structural Typing (Row Polymorphism)

Objects are typed by their shape. A function that reads `.name` works on anything with a `name` field, regardless of what else the object carries:

```javascript
function getName(obj) { return obj.name; }
var person = {name: "Alice", age: 30};
var dog = {name: "Rover", breed: "Labrador"};
var n1 = getName(person);
var n2 = getName(dog);
```

```
function getName<a, b>({name: a | b}) => a
var n1: String
var n2: String
```

The row variable `b` ranges over the rest of the object's fields; the function commits only to the existence of `name`.

### Operator Overloading (Type Classes)

`+` works on `Number` or `String`; `[]` works on `Array`, `String`, `Map`, or any indexable row. Both are encoded as type classes (`Plus`, `Indexable`) — the function is polymorphic in any instance, but the call site fixes a single one.

### Method Chaining & Builders (Equi-recursive Types)

Methods that `return this` produce equi-recursive types: the method's `this` parameter is unified with the object containing the method, so the chain types itself.

```javascript
var requestBuilder = {
    url: "",
    method: "GET",
    setUrl: function(u) { this.url = u; return this; },
    setMethod: function(m) { this.method = m; return this; },
    send: function() { return this.method + " " + this.url; }
};
var response = requestBuilder.setUrl("/api/users").setMethod("POST").send();
```

minfern infers `setUrl` as `this: {url: String | c} => (String) => {url: String | c}` — the row variable `c` carries the rest of the builder along through the chain.

### Control-Flow Joins (Union Types)

Branches of an `if`, ternary, or array literal that disagree in type are *joined* into a closed union. Reading a member or indexing into a union pushes the operation through every member.

```javascript
function f(b) { return b ? 42 : "err"; }
```

```
function f<a>(a) => Number | String
```

Same mechanism handles multiple return types and mixed arrays:

```javascript
function f(b) { if (b) { return 1; } else { return null; } }
var a = [1, "two", 3];
var v = [1, "two"][0];
```

```
function f<a>(a) => Number | Null
var a: Number | String[]    // i.e. (Number | String)[]
var v: Number | String
```

For object branches with disjoint shapes, the union member access joins the available fields:

```javascript
var pt = b ? {x: 1, y: 2} : {x: 3, z: 4};
var x = pt.x;
```

```
var pt: {x: Number, y: Number} | {x: Number, z: Number}
var x: Number    // both branches expose `x: Number`
```

### Discriminated Unions & Narrowing (Predicate Refinement)

`typeof e === "..."`, `e === literal`, and `e.kind === "..."` *refine* a union-typed binding within a branch. Use this to write the canonical tagged-union pattern:

```javascript
/** function area(s: {kind: "circle", r: Number}
                   | {kind: "square", s: Number}) => Number */
function area(shape) {
    if (shape.kind === "circle") { return shape.r; }
    else                          { return shape.s; }
}
```

This type-checks: inside the `if` branch, `shape` is narrowed to `{kind: "circle", r: Number}` so `shape.r` is well-defined. In the `else`, the negated predicate narrows it to `{kind: "square", s: Number}`.

`switch` on a literal-union discriminant gets the same narrowing per case, plus exhaustiveness analysis: a switch with no `default` whose cases don't cover every literal of the discriminant produces a warning.

The `Array.prototype.find` builtin returns `T | undefined`, so the caller has to narrow before using the result:

```javascript
var arr = [1, 2, 3];
var v = arr.find(function(x) { return x > 0; });
var pick = (typeof v === "undefined") ? 0 : v;
```

```
var v: Number | Undefined
var pick: Number
```

### Modules (ES `import` / `export`)

minfern resolves `import` statements relative to the importing file's
directory and threads inferred types across the module graph. Visibility
is explicit: only what's marked `export` is reachable from another
file, and importing a private binding is a structured error.

```javascript
// identity.js
export function id(x) { return x; }

// app.js
import * as ns from "./identity.js";
var n = ns.id(42);
var s = ns.id("hello");
```

```
var n: Number
var s: String
```

`import * as ns` builds a first-class module type rather than an object,
so each `ns.foo` access re-instantiates the export's scheme — `ns.id`
stays polymorphic across uses. Default imports, named exports and
imports (with renaming), `export default`, and re-exports
(`export … from`, `export * from`, `export * as ns from`) are all
supported. See [modules.md](modules.md) for the full design and
`examples/modules/` for runnable fixtures.

## Unsupported JavaScript Idioms

A binding's type is fixed at declaration. Operators that combine values still need their operands' types to agree. Output below is verbatim from `minfern --no-color`.

**No variable type changes.** Assignment unifies with the binding's existing type.

```javascript
// ❌ Rejected
var x = 1;
x = "hello";
```

```
Error: Type mismatch: expected 'Number', found 'String'
   ╭─[ <stdin>:2:1 ]
   │
 2 │ x = "hello";
   │ ─────┬─────
   │      ╰─────── Type mismatch: expected 'Number', found 'String'
```

**No type coercion at `+`.** The `Plus` class requires both operands to be the same instance.

```javascript
// ❌ Rejected
var msg = "Count: " + 42;
```

```
Error: Type mismatch: expected 'Number', found 'String'
   ╭─[ <stdin>:1:11 ]
   │
 1 │ var msg = "Count: " + 42;
   │           ───────┬──────
   │                  ╰──────── Type mismatch: expected 'Number', found 'String'
```

**No `&&` / `||` between values of different types.** `&&` and `||` return one of their operands and minfern unifies them, so `1 && "hi"` is rejected. The default-value pattern `name || "Guest"` only works when `name` is also `String`.

```javascript
// ❌ Rejected
var x = 0 || "fallback";
```

```
Error: Type mismatch: expected 'Number', found 'String'
   ╭─[ <stdin>:1:9 ]
   │
 1 │ var x = 0 || "fallback";
   │         ───────┬───────
   │                ╰───────── Type mismatch: expected 'Number', found 'String'
   │
   │ Help: In JavaScript, `||` returns one of its operands
   │       (not a boolean), so both operands must have
   │       compatible types.
   │
   │       Left side has type:  Number
   │       Right side has type: String
```

**No optional properties on inferred row types.** Object literals produce *closed* rows: a property that wasn't written into the literal can't be read out.

```javascript
// ❌ Rejected
var u = {name: "Bob"};
var age = u.age;
```

```
Error: Property 'age' not found in type {name: String}
   ╭─[ <stdin>:2:11 ]
   │
 2 │ var age = u.age;
   │           ──┬──
   │             ╰──── Property 'age' not found in type {name: String}
```

(Optional values exist for built-ins that explicitly return them, e.g. `Array.prototype.find` returns `T | undefined`. See the narrowing example above.)

**Narrowing requires an explicit union type.** `if (typeof x === "string")` only refines `x` if `x`'s type is already a union containing `String`. Without an annotation, the parameter is inferred from the branch bodies, and the condition can't widen it after the fact.

```javascript
// ✅ Works (annotation makes x a union)
/** function f(x: String | Number) => Number */
function f(x) {
    if (typeof x === "string") { return x.length; }
    else                        { return x; }
}
```

## Supported Syntax

Quick reference for the JavaScript surface minfern accepts:

| Category       | What works                                                                                                |
|----------------|-----------------------------------------------------------------------------------------------------------|
| Literals       | template literals, regex literals                                                                         |
| Variables      | `var`, `const`, `let` (treated as `var` — block scoping isn't modelled)                                   |
| Functions      | declarations, expressions, arrow functions, method shorthand, getters/setters                             |
| Destructuring  | object and array (desugared at parse time)                                                                |
| Iteration      | `for`, `while`, `do-while`, `for-in`, `for-of`                                                            |
| Classes        | declarations only, desugared into factory functions; no inheritance, no `static` members                  |
| Async          | `async`/`await`, desugared via `Promise.resolve`                                                          |
| Modules        | ES `import`/`export` — see [Modules](#modules-es-import--export) above                                    |
| Annotations    | inline `var x /*: T */` and doc-comment `/** var x: T */` — see [declare.md](declare.md)                  |

## Future Work

Some of the limitations above are annoying and may be worth supporting in some way or form. It would be nice to support nullable/optional-style union types directly on object properties, and to make `&&`/`||` flow narrowing-aware. It would require some work to avoid losing the principal typing property (every expression has a single unambiguous most general type).

Not yet supported: spread/rest parameters, class inheritance, static class members.

## Self-testing

minfern is heavily tested against itself: every operator's typing rule is cross-checked against an operational semantics, and a property test generates well-typed programs by construction and reduces them to verify they never get "stuck". See [ARCHITECTURE.md](ARCHITECTURE.md) for the module layout and the four test layers.
