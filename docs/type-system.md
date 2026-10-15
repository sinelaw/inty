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
function getName<a, b> where a has {name: b} => (a) => b
var n1: String
var n2: String
```

`a has {name: b}` is a *property constraint* (`HasProp` internally): `getName` works on any `a` from which reading `.name` gives a `b`. That's any object with a `name` field, whatever else it carries — and, for a property built-in types have, a string or an array too:

```javascript
function lastChar(s) { return s.slice(s.length - 1); }
lastChar("abc");     // String: a string has `slice` and `length`
lastChar([1, 2, 3]); // Number[]: so does an array
lastChar(42);        // error: a number has neither
```

inference doesn't decide what `obj` is when it meets `obj.name` on a value whose type isn't known yet. It records the constraint and resolves it once the type is known: a string's or array's built-in property (each read gets its own copy of a built-in method's type, so `s.slice(i)` and `s.slice(i, j)` can both be called on the same parameter), or an object's field. A constraint still open when the function is generalised becomes part of its type, like `Plus` below; the receiver determines the result, so a constraint on a variable the environment fixes fixes its result too (see `env_fixed_vars`). A receiver nothing ever pins down is read as an object with that field, which is what inty inferred for every property access before `HasProp`.

An object spread (`{a: 1, ...o}`) takes the operand's fields over the ones before it. When the operand's type isn't known yet (a parameter nothing else constrains), which fields it writes over is decided at each use, once it is: a `Spread` constraint in the function's scheme, as `HasProp` is for a property read. So `function f(o) { return {a: 1, ...o}; }` accepts `f({})` (whose `a` is a `Number`), `f({a: 2})` and `f({a: "s"})` (whose `a` is a `String`), and `function g(o1, o2) { return {...o1, ...o2}; }` gives `g({a: "s"}, {a: 1}).a` the type `Number`. When the operand's shape is only partly known (a parameter whose fields are read), it may or may not have `a`, so the result's `a` is the literal's only if `o`'s `a`, when there is one, has the same type, and two such operands must agree on the fields neither names. An operand is an object: spreading a function is an error (a spread copies own properties, never a call signature).

### Operator Overloading (Type Classes)

`+` works on `Number` or `String`; `[]` works on `Array`, `String`, `Map`, or any indexable row, and storing through it (`c[i] = v`) on any of them but a `String`, whose characters are read-only (`IndexWrite`). A property store (`r.p = v`) needs an object (`FieldWrite`): a string's, an array's or a function's built-in properties aren't assigned, but for an array's `length`, which takes a number and truncates the array (`xs.length = 0` clears it; a larger length would leave holes, a fault like a read past the end). Both are encoded as type classes (`Plus`, `Indexable`) — the function is polymorphic in any instance, but the call site fixes a single one. `+` takes two operands of one type, and `Plus a` says that type is a number or a string, so `function add(x, y) { return x + y; }` is `<a> where Plus a => (a, a) => a`: `add(1, 0.5)` is a `Number`, `add("a", "b")` a `String`, and `add(1, "b")` an error. Property reads on values of unknown type (`HasProp`, above) are a third, structural class.

A scheme's constraints are part of its written form, so declarations carry them: `inty declarations` prints `/** const add: <a, b, c> where Plus a b c => (a, b) => c */`, and the annotation parser reads the `where` clause back (`Plus t`, short for `Plus t t t`, `Indexable t i e`, `t has {name: T, …}`), so a consumer of the `.d.js` is held to them. A `Plus` on a type that is already known is decided when the binding is generalised rather than carried into its scheme, so `const f = function () { return g + g; }` with `g` a function is an error even if `f` is never called.

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

`T | Null` and `T | Undefined` are *sums*, as in the Lean model (`lean/Inty/Types.lean`, `Nullable` and `Optional`): a type of their own, holding either nothing or a `T`. However a union mentions `null` or `undefined`, it is the same sum — `T | Null | Undefined` is `Nullable (Optional T)` — and it prints as the union it reads as. A postfix `?` in a type annotation is `T | Undefined`.

- **Putting a value in.** Where a sum is expected (an annotation, a parameter, a declared return), a `T`, the sum's nothing, or the sum itself is accepted. A value whose type isn't known yet waits, as the constraint `Inject τ (T | Null)`, until its type is (binding it to the sum would guess). A sum is never unified with what it holds: a `Number | Null` is not a `Number`, and a `Number` variable doesn't become one.
- **Getting it out.** `x ?? d` is what `x` holds besides nothing, joined with `d`'s type; `x != null` (and the other tests below) narrows `x` to it in the branch. For an `x` whose type isn't known yet, that is the `σ` of the constraint `Strip τ σ`, which waits for `τ` (a sum gives its value, any other type itself). An `x` that is always nothing (`null ?? d`) is an error.

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

### Unions: declared, not guessed

Branches that must produce one value — the two sides of a conditional, the `return`s of a function, the elements of an array literal, the sides of `??` — must have **one type**, as in Hindley–Milner and the Lean model. inty doesn't guess that disagreeing branches form a union: whether such a guess succeeds could depend on what happens to be known about each side at that point, which makes the verdict depend on statement order.

```javascript
function f(b) { return b ? 42 : "err"; }
// error: Branches have different types: '42' and '"err"'
```

A union is made by saying so. Where an annotation gives the expected type, each branch is *checked* against it instead of being joined:

```javascript
/** function f(Boolean) => Number | String */
function f(b) { return b ? 42 : "err"; }

/** const mixed: (Number | String)[] */
var mixed = [1, "two", 3];

/** var pt: {x: Number, y: Number} | {x: Number, z: Number} */
var pt = b ? {x: 1, y: 2} : {x: 3, z: 4};
var x = pt.x;    // Number — both arms expose `x: Number`
```

The join rules, none of which guesses:

- literals of one base type widen to it (`b ? 1 : 2` is `Number`; also inside tuples and objects);
- a value of a (declared) union or sum joined with one of its arms is that union or sum;
- a branch that doesn't complete (`return`, `throw`) contributes nothing, and statements (`if (c) n += 1; else break;`) aren't joined by value at all;
- a conditional one of whose branches is exactly `undefined` (or `null`) is the other branch's type or nothing: `xs.length > 0 ? xs[0] : undefined` is `Number | Undefined`, `c ? "a" : null` is `String | Null`. The branch itself says which sum, so nothing is guessed.

Other branches that are `null` or `undefined` — the `return`s of a function, an element, a side of `??` — are no exception: the sum is said, and each branch is injected into it.

```javascript
function find(xs, v) { for (const x of xs) { if (x === v) return x; } return null; }
// error: Branches have different types

/** function find<a>(xs: a[], v: a) => a | Null */
function find(xs, v) { for (const x of xs) { if (x === v) return x; } return null; }
var hit = find([1, 2], 2);    // Number | Null
```

A value whose type isn't known yet is unified with the other side, including a parameter whose properties are read (`HasProp`):

```javascript
function h(o, b) { const v = b ? o : "str"; return o.x; }
// error: Property 'x' not found in type String — `o` is joined with a
// String, so it is one; annotate `v` (or `o`) if a union is meant.
```

Reading a member of, or indexing into, a union pushes the operation through every arm; there the results do form a union (`{x: Number} | {x: String}` read at `.x` is `Number | String`) — derived from one that was declared. Unification itself is equality: a union is not any one of its arms. A value of an arm is accepted where the union is expected by *subsumption*, but a `String | Number` is never accepted where a `String` is needed.

In JavaScript annotations a class's name is its type (`/** const xs: (A | B)[] */`); Python annotations already name classes (`x: Dog | Cat = …`).

A class's type takes a type argument for each type its constructor and methods leave generic — a field set from a constructor parameter, the receiver of a method that reads `this` — though the class declares none. `class Box { constructor(v) { this.v = v; } }` is `Box<T>`: write `Box<Number>`, or pass a type parameter through (`/** function f<A>(b: Box<A>) => A */`). The error for a bare `Box` says which fields and methods the arguments come from.

`&&` and `||` return one of their operands. When both operand types are known, the result is what can come out: `a && b` is the falsy part of `a`'s type together with `b`'s, `a || b` the truthy part together with `b`'s. So `cond && maybeObj` (a `Boolean` and an `Undefined | {…}`) is `Boolean | Undefined | {…}`, fine as a test, and `name || "Guest"` with `name: String` is a `String`. An object, array or function is always truthy, so `obj && obj.x` is just `obj.x`'s type. With an operand whose type isn't known yet the two must agree, as before: nothing is guessed. The right operand is checked in the environment the left one leaves (`found && found.v` reads `v` of the narrowed `found`).

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

The other predicates that narrow:
- `x === null` and `x !== undefined`, read by the *type* of the other operand, so a local `const undefined = 0` doesn't count;
- `x == null` / `x != null`;
- truthiness (`if (x)`, `!x`), with each language's rules;
- `&&`, `||` and `?:`, including their right operands (`q !== null && q.x > 0`).

A test also narrows:
- the code after an `if` whose other branch always returns, throws, breaks or continues (`if (q === null) return 0; return q.x;`);
- the body of a `while` or `for` loop, and the code after a loop that has no `break`.

**Only bindings that never change are narrowed.** Narrowing applies to `const`s, parameters that the function never reassigns, and `let`s that are never reassigned. For any binding that is written after its initialiser, a test says nothing. This is Typed Racket's rule: a fact about a value holds as long as the value is the same, so a narrowing never has to end — not after an assignment, not in a loop, and not inside a closure that runs later. [docs/flow-narrowing-safe.md](flow-narrowing-safe.md) has the full argument. To narrow a variable you update, copy it into a `const` first.

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

**Fields are set in order.** JavaScript sets a class's fields one by
one, the class-body initialisers first and then the constructor's
`this.f = …` lines, on an instance whose later fields aren't set yet. So
in an initialiser (or the value of a constructor's `this.f = …`) `this`
may only be read as `this.f`, of a field set before it, and reads the
value that field was set to. Reading a later field, calling a method
(`this.m()`, which may read one), passing `this` on, or a function that
uses `this` is rejected. The exception is an initialiser that is a whole
arrow function, `f = () => this.n`: it runs later, on the finished
instance, and is typed as a method of the instance (its own property).
The constructor's body is still limited to `this.f = …;` lines.

```javascript
class P {
  x = 1;
  y = this.x + 1;           // ok: x is set before
  f = () => this.x + this.y; // ok: runs on the finished instance
  constructor(n) { this.z = this.y + n; }
}
class Q { a = this.b; b = 1; }        // rejected: b isn't set yet
class R { a = this.m(); m() { return 1; } } // rejected: a method call
```

**Methods and getters are on the prototype.** A class's methods and
`get foo() { … }` getters aren't the instance's own properties: a spread
`{...instance}` doesn't copy them, and a store to one is rejected (it
would make an own property where the type says there is none). The
instance's fields are its own and may be stored to. A field with the
same name as a method or getter is rejected. In an object literal, a
method shorthand is the object's own property, and a getter is its own
too. A store to any getter is rejected (it throws in strict code); a
spread copies the getter's value. A function reading a property accepts
an object with either kind. Setters (`set foo(v) { … }`) are rejected:
a store would run code inty doesn't model.

**`new`.** Only `new` calls a class (a call without it throws), so
`C(1)` is rejected. A class's type prints as `new (params) => Instance`,
and an annotation can declare a constructor so: `/** const C: new
(Number) => {n: Number} */`. `new F(…)` of any function gives back what
`F` returns, which must be an object: in JavaScript a primitive result is
replaced by the new object, so a function returning one can't be called
with `new`. A function that uses `this` (a pre-class constructor
function, `function F() { this.n = 1; }`) can't be called with `new`
either: inty has no type for the object it would fill in.

**No inheritance.** `class Sub extends Base { … }` is rejected. A
class's methods are checked with its instance as `this`, and the
instance's type says which fields it lacks (a spread of `this` relies on
that), so a base method would not be safe on a subclass instance, which
has more. Write a factory that builds the object instead (see
[examples/spa/gaps.md § "By design"](../examples/spa/gaps.md)).
`static` members are rejected too.

**External classes.** A class implemented elsewhere is declared without a
body, by a `class` annotation, as `/** const X: T */ const X;` declares a
value:

```javascript
/** class Point(x: Number, y: Number) { x: Number, y: Number, norm: () => Number } */
class Point;
/** class Gain extends AudioWorkletProcessor { gain: Number } */
class Gain;
```

It is a constructor taking the parameters (or, without them, its base's)
whose instances have the members and, with `extends`, every field of the
base's instances a member doesn't redeclare. A member of function type is
a method on the prototype (not copied by a spread, not stored to); the
modifiers `proto` and `readonly` declare another member so, as for a
getter: `{ proto readonly area: Number }`. Only such a declaration
extends, and only a class or constructor itself declared without a body:
no code inty checks runs with another class's instance as `this`.

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

Resolution order: a relative or absolute path names a file; any other
specifier goes through the exact-match `paths`, then the wildcard
`paths` (most specific first), then the nearest `package.json`'s
`"imports"` (Node's `#name` subpath imports, conditions and `*` patterns
included; a `.d.js` next to the mapped `.js` is preferred, since the
runtime file is usually untyped), then a same-named file, then
`baseUrl`. A mapped specifier wins over a file of the same name, as in
Node. Third-party `.d.js` stubs live wherever the `paths` map points;
inty doesn't ship npm-package types itself.

Each module is checked once per run, and every importer sees the same
module: its state (a mutable exported object) is shared, so two
importers' uses of it must agree. A module's leftover constraints are
solved when it has been checked, so an error in it is reported in it;
an integer-literal field its importers write a fraction into is a
`Number`, as in one file. `inty a.js b.js …` checks several files in one
run the same way.

### Faults

inty's guarantee is that a program it accepts doesn't go wrong: it never
calls what isn't a function, reads a property a value doesn't have, or
mixes values of different types. It may still stop at one of these
faults, which are not violations of that guarantee:

| Fault | Where | In `dynamics` | In the Lean model |
|---|---|---|---|
| Out of bounds | an element read at an index an array or a string hasn't, or a store past an array's end (see [Primitive and compound types](#primitive-and-compound-types)) | `Stuck::OutOfBounds` | `Fault.outOfBounds` |
| An uncaught exception | a `throw` no `catch` catches | `Stuck::UncaughtThrow` | `Result.thrown` |
| Out of fuel | `dynamics`'s step limit (a program that doesn't end) | `Stuck::FuelExhausted` | `Result.timeout` (its clock) |

The model's soundness theorem (`lean/Inty/Soundness.lean`, `eval_sound`)
says a well-typed program ends in a value of its type or in one of these,
and never gets stuck otherwise.

## Unsupported JavaScript Idioms

A binding's type is fixed at declaration. Operators that combine values still need their operands' types to agree. Output below is verbatim from `inty --no-color`.

**No variable type changes.** Assignment unifies with the binding's existing type. A `let` or `var` that is assigned after its initialiser has one type, never a polymorphic one: `let id = function (x) { return x; }` can be called at two types only if it is never reassigned, as a `const` can.

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

**No reading a record with a key known only at run time.** `o[k]` on a record needs `k` to be a literal (`o["x"]` reads the field `x`, as `o.x` does). A string variable may name no field, and then the read gives `undefined`. An object used as a string-keyed map is a `Dict<V>`, whose read gives `V | Undefined` (see [Primitive and compound types](#primitive-and-compound-types)).

```javascript
// ❌ Rejected
const o = {x: "s", y: "t"};
function get(k) { return o[k]; }

// ✅ Accepted
/** const d: Dict<String> */
const d = {x: "s", y: "t"};
function get2(k) { return d[k] ?? ""; }
```

```
Error: Type '{x: String, y: String}' is not an instance of Indexable (a key known only at run time may name no field: use a literal key, or a `Dict<V>`)
   ╭─[ <stdin>:2:26 ]
   │
 2 │ function get(k) { return o[k]; }
   │                          ──┬─  
   │                            ╰─── Type '{x: String, y: String}' is not an instance of Indexable (a key known only at run time may name no field: use a literal key, or a `Dict<V>`)
───╯
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
/** var pair: [String, Number] */     // tuple
/** var gains: Dict<Number> */        // plain object used as a map; also `{ [String]: Number }`
/** var seen: Set<String> */          // the instance types of `new Map()` / `new Set()`
/** var index: Map<String, Number> */
```

Built-in type names: `Number`, `String`, `Boolean`, `Null`, `Undefined`. Unknown identifiers are rejected (typos like `Stirng` are an error, not a fresh variable).

**Numbers** are one type, `Number`, as in JavaScript: an integer and a fraction are both `Number`s, arithmetic takes and gives `Number`s, and an index is a `Number`. Whether a number is always an integer is not a matter of types. A code generator that wants machine integers works it out from where values flow: the Go backend computes in Go `int`s wherever a number is always an integer (see `crates/inty-go/src/kinds.rs`), so indices and loop counters are machine integers without an annotation saying so. That analysis can't reject a program: it only decides how a number is stored. (`Int` was a type of its own; an annotation that names it is now an error that says to write `Number`.)

Reading an array's or a string's element at an index it hasn't (`xs[xs.length]`, `xs[-1]`, `xs[0.5]`), or storing an array's element past its end, is a fault: an element read has the element type, not `T | Undefined`, so the program stops there rather than run on with an `undefined` (the Go backend panics; JavaScript reads `undefined`, or makes a hole). A store just past the end (`xs[xs.length] = v`) appends.

A **tuple** `[A, B]` is a fixed-length array whose elements have their own types. An array literal where one is expected is one; `t[0]` with a constant index reads that element, and `const [a, b] = t` destructures it. An array literal with elements of different types and no annotation is an error that suggests a tuple (or a record, or an element union).

A **`Dict<V>`** is a plain object used as a string-keyed map (`{ [String]: V }` is the same type). An object literal where one is expected is one (each value must fit `V`); reading a key, `d.k` or `d[k]`, gives `V | Undefined`, since the key may be missing (`d.k ?? 0`); storing one, `d.k = v` or `d[k] = v`, takes a `V` (not `undefined`, which `Object.values` would then return; an update such as `d.k += 1` reads the entry first, so it needs it narrowed); `Object.keys`, `Object.values(d)` (`V[]`), `Object.entries(d)` (`[String, V][]`) and `Object.fromEntries` work on it.

Typed arrays are `Int32Array`, `Uint8Array`, `Float32Array` and `Float64Array`. Each is its own type, not an ordinary array:
- It has a fixed length: `.length`, `.fill(v)`, `.subarray(start?, end?)`, `.slice(start?, end?)`, `.set(other, offset?)`, `.buffer` and `.byteLength`, but no `push`.
- Indexing `a[i]` takes a number index, and reads a `Number`.
- A store into an integer array takes any number and wraps it to 32 or 8 bits, as JavaScript's `ToInt32` / `ToUint8` do (`a[0] = 1.5` stores 1).
- They are made with `new Int32Array(n)` or `Int32Array.from(xs)`.

### Function types

A function-type annotation is `(P1, P2, ...) => R`. Parameter names are optional. For functions, both forms below are accepted:

```javascript
/** function add(x: Number, y: Number) => Number */
function add(x, y) { return x + y; }

/** const inc: (Number) => Number */
const inc = function(k) { return k + 1; };
```

A function type, `(Number) => Number`, is of a function that uses no `this`: an arrow, or a function that doesn't mention `this`. It can be called on an object, called detached or passed on, wherever it is: an annotated function, a `const`, a parameter or result, or a member of an object type. So a record field can hold a callback:

```javascript
/** const s: { stop: () => Undefined } */
const s = { stop: () => undefined };
/** function set(stop: () => Undefined) => Undefined */
function set(stop) { s.stop = stop; }
const end = s.stop;
end();                 // detached
s.stop();              // on the object
```

A function that reads `this` doesn't have such a type: `/** const f: (Number) => Number */ const f = function (n) { return this.x + n; };` is rejected, since `f(1)` throws.

- A method says its `this` as a first parameter, as TypeScript's `this: T`: `(this: T, n: Number) => Number` is called on a `T`, which it may read as `this`. An object type whose methods read the object names itself: with `/** type O = {x: Number, m: (this: O, n: Number) => Number} */` and `/** const o: O */`, `m` may read `this.x`, and `o.m(1)` is accepted, but `const g = o.m; g(1)` isn't: `g` is a method, and calling it detached passes `this` = undefined. TypeScript's method signature, `m(n: Number): Number`, which leaves `this` unsaid, is an error that says how to write it.
- A body says whether a function is a method: one that mentions `this` is. A type, which has no body, says it: a function type without `this:` is of a function that uses none, in an annotation and in a declaration (`.d.js`) alike. So the standard library declares the host methods that throw when called detached (`Storage`'s, `Location`'s, `History`'s, `Map`'s, `Set`'s, the canvas context's and a gradient's) with their `this`, and `const g = localStorage.getItem; g("k")` is rejected. A type for such an object names the library's (`type Ctx = CanvasRenderingContext2D<…>`): one that describes part of it with plain function fields doesn't fit, since the object's methods need it. Elements, events and audio objects don't say theirs yet.
- A method and a function that uses no `this` are different types, so they don't join (as an array's elements, or a conditional's branches): one or the other could then be called the wrong way.
- An object literal's method that doesn't mention `this` uses none; one that does reads the object.
- A declaration without a body (`.d.js`) and a built-in method keep their own `this`, but the functions they are given use none. So `[1, 2].map(o.m)` is rejected when `o.m` reads `this`, as JavaScript throws there.

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

An alias may refer to one declared after it, in the same file or a `--lib` file (as may a class). An alias that refers to itself, directly or through others, is a recursive (equi-recursive) type, printed by its name:

```javascript
/** type Tree = { label: String, kids: Tree[] } */
/** type List<T> = { head: T, tail: List<T> | Null } */
```

One defined as itself (`type Bad = Bad`) is an error.

`/** nominal type InsertIx = Number */` declares a *nominal* type instead: a brand that keeps its identity through unification (an `InsertIx` is not a `TrackIx`, nor a `Number`), while comparisons and field access see through it. See [patterns.md](patterns.md#brand-newtypes).

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
| Variables      | `var` (function-scoped), `const`, `let` (block-scoped; a `for (const x of …)` binding is the loop body's)  |
| Functions      | declarations, expressions, arrow functions, method shorthand, default params (`x = 1`), destructuring defaults (`{a = null}`), rest (`...args`), spread in calls (`f(...arr)`) |
| Destructuring  | object and array, with defaults; rest patterns (`{a, ...rest}`, `[head, ...tail]`)                        |
| Iteration      | `for`, `while`, `do-while`, `for-in`, `for-of`                                                            |
| Classes        | declarations + `export default class`, instance methods, fields, getters (no setters), private fields (`#x`) (see [Class Bodies](#class-bodies-fields-private-fields-accessors)), external classes declared without a body (`/** class X extends B { … } */ class X;`); no `extends` in a class with a body, no `static` members |
| Async          | `async`/`await`, `export async function`, desugared via `Promise.resolve`                                 |
| Errors         | `try` / `catch (e)` / `catch {}` (binding optional) / `finally`; `e` may be any thrown value, so its type is opaque: it can be passed on, tested and rethrown, but not used as a number, string or object |
| Primitive methods | the `String.prototype` and `Array.prototype` methods (`replace`/`replaceAll` take a string or a function of the match, `(String) => String`: the capture groups and offset JavaScript also passes have pattern-dependent types and aren't modelled — read them from `match`/`exec` instead); on numbers `toFixed`, `toPrecision`, `toExponential`, `toString(radix?)`, `toLocaleString`, `valueOf`; on booleans `toString`, `valueOf` |
| ASI            | inserted before `return` / `break` / `continue` / `throw` / postfix `++` / `--` when a line terminator separates the next token |
| Rejected       | `delete` (soft type-time diagnostic pointing at workaround — accepted by the parser, the expression's result is `Type::Error` so the rest of the file still checks); `super.member`, `static` members |
| Modules        | ES `import`/`export` with `inty.json` paths/baseUrl — see [Modules](#modules-es-import--export) above     |
| Annotations    | inline `var x /*: T */`, doc-comment `/** var x: T */`, postfix `T?` for `T \| Undefined` — see [../declare.md](../declare.md) |

The Python and Lua frontends accept a smaller surface chosen so every construct
lowers cleanly onto the same AST; see the module-level docs in
`crates/inty/src/frontends/python/mod.rs` and
`crates/inty/src/frontends/lua/mod.rs` for the per-language lists.
