# Type system

inty's inference engine is language-agnostic: every frontend lowers its surface
syntax onto a shared AST, and inference works on that AST. The examples below
use JavaScript syntax, but the underlying rules apply to the Python and Lua
frontends too.

## Features

### Full Type Inference

No annotations required — every type is inferred. Annotations are accepted (in JSDoc comments or inline) for documentation; inty can also emit them for you.

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

`function id(x) { return x; }` works with any type. inty infers `id<a>(a) => a`:

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

inty infers `setUrl` as `this: {url: String | c} => (String) => {url: String | c}` — the row variable `c` carries the rest of the builder along through the chain.

### Callable Rows (Functions with Statics)

Function values are rows. A plain function is a row carrying only an internal call signature; a constructor with statics is the same row plus extra named fields. So `String("hi")` and `String.fromCharCode(65)` both work uniformly: the call peels the row's call signature, the member access reads the named field — no special case for "constructor types."

```javascript
const c = String.fromCharCode(65);   // c : String
const s = String(42);                // s : String
const arr = [1, 2, 3];
const stringified = arr.map(String); // stringified : String[]
```

The last line is the payoff: passing `String` (a row carrying a call signature plus statics) where `arr.map` expects a function works via plain row polymorphism. No subtyping rule, no callable-vs-row asymmetry — `Type::Func` is purely a sub-component of a row, never a top-level value type.

In `.d.js` declarations, callable rows use a TS-style keyless call signature inside the row body:

```javascript
/** const String: <T> {
        (T) => String,
        fromCharCode: (Number) => String,
        fromCodePoint: (Number) => String
    } */
const String;
```

### Nullable / Optional Values (Postfix `T?`)

A postfix `?` in a type annotation desugars to `T | Undefined`. Composes with the existing union machinery — narrowing, `?.`, `??` — without introducing a new nominal type.

```javascript
/** function getNum(arr: Number[]) => Number? */
function getNum(arr) {
    return arr.find(function(n) { return n > 0; });
}

/** function safe(arr: Number[]) => Number */
function safe(arr) {
    return getNum(arr) ?? 0;
}
```

For DOM-style APIs that return `null` (not `undefined`), write the long form `Element | Null` explicitly — `?` adds `Undefined` only, matching TypeScript's `?:` convention.

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

### Sum Types: Discriminated Unions & Narrowing (Predicate Refinement)

`typeof e === "..."`, `e === literal`, and `e.kind === "..."` *refine* a union-typed binding within a branch. Use this to write sum types in the canonical tagged-union style — a single value that is exactly one of several known shapes, distinguished by a literal discriminator:

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

### Class Bodies: Fields, Private Fields, Accessors

Class declarations desugar to factory functions returning a row of
methods + fields. `#name` private fields lower to a sentinel-keyed
row entry that JS source can't tokenise — accessible from inside the
class body via the parser's lowering, unreachable from outside. The
type printer renders the sentinel back as `#name` so error messages
stay readable.

```javascript
class Counter {
  #count = 0;
  inc() { this.#count = this.#count + 1; return this.#count; }
  get current() { return this.#count; }
}
const c = new Counter();
const n = c.inc();   // n : Number
const v = c.current; // v : Number
```

Cross-instance private access works the same way:

```javascript
class Pair {
  #x;
  combineWith(other) { return this.#x + other.#x; }   // both peeled to the same sentinel
}
```

Outside the class body, `obj.#name` is a parse-time error. Two
unrelated classes that both declare `#x` share the storage key
under the current pragmatic lowering — collisions are rare in
practice; per-class suffix is a future option.

`get foo() { … }` accessors lower to a regular field whose value
is the body's IIFE — `obj.foo` reads its return type. `set foo(v)
{ … }` is parse-accepted but the field is not declared from the
setter (initialise via `this.foo = …` in the constructor).

### Modules (ES `import` / `export`)

inty resolves `import` statements relative to the importing file's
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
supported. See [../modules.md](../modules.md) for the full design and
`examples/modules/` for runnable fixtures.

#### Path aliases and stub packages (`inty.json`)

Bare specifiers (`@hotwired/stimulus`) and root-relative names
(`controllers/foo`) resolve via an optional `inty.json` at any
ancestor of the importing file. The format mirrors tsconfig-paths:

```jsonc
{
  "baseUrl": "./src",
  "paths": {
    "@hotwired/stimulus": ["./inty-stubs/@hotwired/stimulus.d.js"],
    "controllers/*":      ["./controllers/*"]
  }
}
```

Resolution order: direct relative/absolute → exact-match `paths` →
wildcard `paths` → `baseUrl`. Third-party `.d.js` stubs live wherever
the `paths` map points; inty doesn't ship npm-package types itself.

## Unsupported JavaScript Idioms

A binding's type is fixed at declaration. Operators that combine values still need their operands' types to agree. Output below is verbatim from `inty --no-color`.

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

**No `&&` / `||` between values of different types.** `&&` and `||` return one of their operands and inty unifies them, so `1 && "hi"` is rejected. The default-value pattern `name || "Guest"` only works when `name` is also `String`.

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

(Optional values exist for built-ins that explicitly return them, e.g. `Array.prototype.find` returns `T | undefined`. See the narrowing example above. Annotations can use the postfix `T?` sugar for `T | Undefined`: `/** function getUser(): User? */`.)

**Narrowing requires an explicit union type.** `if (typeof x === "string")` only refines `x` if `x`'s type is already a union containing `String`. Without an annotation, the parameter is inferred from the branch bodies, and the condition can't widen it after the fact.

```javascript
// ✅ Works (annotation makes x a union)
/** function f(x: String | Number) => Number */
function f(x) {
    if (typeof x === "string") { return x.length; }
    else                        { return x; }
}
```

## Type Annotation Syntax

Type annotations are optional — every type is inferred — but can be written for documentation, narrowing (see [Sum Types](#sum-types-discriminated-unions--narrowing-predicate-refinement) above), or to declare ambient bindings in `.d.js` stubs. Some higher-ranked types *require* a type annotation, but I'm hoping these turn out to be rarely needed.

Two forms of type annotations:

- **Doc-comment statement** preceding a declaration: `/** var x: T */`, `/** function f(...) => T */`, `/** const c: T */`, `/** type Name = ... */`.
- **Inline trailing comment** on a binder or parameter: `var x /*: T */ = 1`, `function f(x /*: Number */) { ... }`.

JSDoc `/** @type {T} */` is also accepted, attached to the next object-literal field. With a `null` or `undefined` initialiser, the field is declared at `T` and the initialiser is treated as a placeholder (matching TypeScript's JSDoc rule). `typeof Helper` inside `T` resolves to the value type of a binding in scope:

```javascript
const api = {
  /** @type {typeof helper} */
  run: null
};
function helper(n) { return n + 1; }
api.run = helper;
api.run(5);                // typed via `@type {typeof helper}`
```

See [jsdoc-at-type.md](jsdoc-at-type.md) for the full rule.

### Primitive and compound types

```javascript
/** var n: Number */
/** var s: String */
/** var b: Boolean */
/** var arr: Number[] */              // Array shorthand
/** var maybe: Number? */             // postfix `?` desugars to `T | Undefined`
/** var u: Number | String */         // union
/** var pt: {x: Number, y: Number} */ // record (closed row)
```

Built-in type names: `Number`, `String`, `Boolean`, `Null`, `Undefined`. Unknown identifiers are rejected (typos like `Stirng` are an error, not a fresh variable).

### Function types

A function-type annotation is `(P1, P2, ...) => R`. Parameter names are optional. For functions, both forms below are accepted:

```javascript
/** function add(x: Number, y: Number) => Number */
function add(x, y) { return x + y; }

/** const inc: (Number) => Number */
const inc = function(k) { return k + 1; };
```

Methods are written as plain fields holding a function; `this` is inferred via row polymorphism (no explicit `this:` annotation):

```javascript
var builder = {
    value: 0,
    setValue: function(v) { this.value = v; return this; },
    get:      function()  { return this.value; }
};
```

### Type parameters (generics)

Quantifiers go at the outermost level (Rank-1):

```javascript
/** const id: <T>(T) => T */
const id = function(x) { return x; };
```

Constraints are not written explicitly: type-class obligations like `Plus a` are inferred from operator use, not declared.

### Type aliases

`/** type Name<P1, P2, ...> = Body */` declares a generic, structural alias. It is substituted at use; aliases are not nominal, so `Pair<Number>` and `{first: Number, second: Number}` are interchangeable.

```javascript
/** type Pair<T> = { first: T, second: T } */

/** const p: Pair<Number> */
const p = {first: 1, second: 2};

/** type Mapping<K, V> = { key: K, value: V } */

/** const makePair: <T>(T) => Pair<T> */
const makePair = function(x) { return {first: x, second: x}; };
```

Nullary aliases are allowed and expanded at use (a bare `Func` resolves to the body, not a fresh variable):

```javascript
/** type S = String */
/** type Func = () => {id: String} */
```

Arity is enforced — `Pair` (no args) or `Pair<A, B>` for the 1-parameter alias above are both errors.

### Callable rows (functions with statics)

A row may carry a keyless call signature plus named fields. Used for things like `String` and `JSON` in stubs:

```javascript
/** const String: <T>{
        (T) => String,
        fromCharCode: (Number) => String
    } */
const String;
```

See `crates/inty/stdlib/core.d.js` for more `.d.js` examples (`Math`, `Object`, `Array`, `Promise`, etc.).

## Supported JavaScript Syntax

Quick reference for the JavaScript surface inty accepts:

| Category       | What works                                                                                                |
|----------------|-----------------------------------------------------------------------------------------------------------|
| Literals       | template literals, regex literals, object property shorthand (`{a, b}`)                                   |
| Variables      | `var`, `const`, `let` (treated as `var` — block scoping isn't modelled)                                   |
| Functions      | declarations, expressions, arrow functions, method shorthand, default params (`x = 1`), destructuring defaults (`{a = null}`), rest (`...args`), spread in calls (`f(...arr)`) |
| Destructuring  | object and array, with defaults; rest patterns (`{a, ...rest}`, `[head, ...tail]`)                        |
| Iteration      | `for`, `while`, `do-while`, `for-in`, `for-of`                                                            |
| Classes        | declarations + `export default class`, instance methods, fields, getters / setters, private fields (`#x`); no inheritance, no `static` members |
| Async          | `async`/`await`, `export async function`, desugared via `Promise.resolve`                                 |
| Errors         | `try` / `catch (e)` / `catch {}` (binding optional) / `finally`                                          |
| ASI            | inserted before `return` / `break` / `continue` / `throw` / postfix `++` / `--` when a line terminator separates the next token |
| Rejected       | `delete` (soft type-time diagnostic pointing at workaround — accepted by the parser, the expression's result is `Type::Error` so the rest of the file still checks); `class extends`, `super`, `static` members |
| Modules        | ES `import`/`export` with `inty.json` paths/baseUrl — see [Modules](#modules-es-import--export) above     |
| Annotations    | inline `var x /*: T */`, doc-comment `/** var x: T */`, postfix `T?` for `T \| Undefined` — see [../declare.md](../declare.md) |

The Python and Lua frontends accept a smaller surface chosen so every construct
lowers cleanly onto the same AST; see the module-level docs in
`crates/inty/src/frontends/python/mod.rs` and
`crates/inty/src/frontends/lua/mod.rs` for the per-language lists.
