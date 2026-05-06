# Gaps found while writing a inty-checked SPA

This started as the list of inty limitations encountered while writing
the todo-list example in this directory. Several of them have since been
fixed — those entries are marked *(resolved)* and kept as a record of
what changed and why.

## Status summary

| # | Gap                                                  | Status       |
|---|------------------------------------------------------|--------------|
| 1 | No function hoisting                                 | *resolved*   |
| 2 | `const x /*: T */;` runtime-unsafe                   | *resolved*   |
| 3 | No nullability / optional types                      | open         |
| 4 | No built-in DOM / `window` / event types             | *resolved*   |
| 5 | No String methods                                    | *resolved*   |
| 6 | No Array methods                                     | *resolved*   |
| 7 | `String` and `String[]` collide under indexing       | open         |
| 8 | Generic row-polymorphic helpers "forget" fields      | open         |
| 9 | Control-flow-dependent return typing is strict       | open         |
| 10| No ergonomic way to seed an empty typed collection   | *resolved*   |
| 11| No arrow functions                                   | *resolved*   |
| 12| No `let`                                             | *resolved*   |
| 13| No destructuring / spread / rest                     | *resolved* (spread/rest open) |
| 14| No `class`                                           | *resolved* (no prototype chain — by design) |
| 14| No `async`/`await`                                   | *resolved*   |
| — | Inline `/*: T */` annotations not captured           | *resolved*   |
| — | Per-field annotations on object literals             | *resolved*   |
| — | Missing Math methods (log/sin/cos/atan2/…)           | *resolved*   |
| — | No `Object.keys`, `Array.isArray`                    | *resolved*   |
| — | No module resolution (`import`/`export`)             | *resolved*   |
| — | No `.d.js` emit from a checked module                | *resolved*   |
| — | `await` outside an async function                    | *resolved* (now errors at parse time) |
| — | Duplicate `const` in the same scope                  | *resolved* (now errors) |
| — | Arrow `this` inheritance / `let` per-iteration / `var` function-scope | **out of scope** (see "By design" below) |
| — | `class extends` / `super` / static methods / private fields | **out of scope** (see "By design" below) |

## Resolved

### 1. No function hoisting *(resolved)*

Previously, `function outer() { return inner(); } function inner() {...}`
failed with `Undefined variable: 'inner'` because inty resolved names
strictly in source order. Mutual recursion between peer functions was
equivalently blocked. The SPA's original workaround was a mutable
`var doRender = function () { ... };` placeholder rewritten at the bottom
of the file.

`infer_stmt_list` now packs adjacent `function` declarations into a
binding group and processes each group in two passes (hoist names with
fresh type variables, infer all bodies, generalise afterwards). Forward
references and mutual recursion between peers now type-check. The SPA
drops the `doRender` placeholder.

### 2. `const foo /*: T */;` without an initializer is a runtime syntax error *(resolved)*

`const x;` is a `SyntaxError` in every browser, so a file using it can
be type-checked but never loaded as a `<script>`. The SPA's workaround
was `var document /*: T */;`, which has its own fragility.

Resolved by the `stdlib/` approach (see gap 4): the `const x;` forms
live in `stdlib/*.d.js`, which the type checker parses but no JavaScript
runtime ever sees.

The related limitation that `/*: T */` inline annotations (as sketched
in `declare.md`) aren't actually captured by the scanner still stands —
only `/** var x: T */` doc-comment annotations are. The stdlib files
use the doc-comment form.

### 4. No built-in DOM / `window` / event types *(resolved)*

inty now ships `stdlib/core.d.js` and `stdlib/dom.d.js`, baked into
the binary via `include_str!` and auto-loaded before every user program.
Users get `document`, `window`, `console`, `Math`, `JSON`, `setTimeout`,
etc. without writing any declarations themselves. Pass `--lib <path>` to
load additional user libs, or `--no-stdlib` to skip the built-in ones.

Still imperfect: the DOM types are a deliberately simplified subset —
`getElementById` returns one flat "Element" shape with all the fields
the SPA uses, because without union types there's no way to distinguish
`HTMLInputElement` from `HTMLDivElement`.

### 5. No String methods *(resolved)*

`escapeHtml` originally looped character-by-character because
`s.replaceAll`, `s.split`, `s.indexOf` and friends were all undeclared.
After the built-in method dispatch in `builtins/mod.rs::string_method_type`,
the SPA's `escapeHtml` is now a five-line `.replaceAll` chain.

Covers `indexOf`, `lastIndexOf`, `substring`, `substr`, `slice`, `split`,
`trim`, `trimStart`, `trimEnd`, `replace`, `replaceAll`, `toUpperCase`,
`toLowerCase`, `charAt`, `charCodeAt`, `startsWith`, `endsWith`,
`includes`, `repeat`, `padStart`, `padEnd`, `concat`, `toString`.

### 6. No Array methods *(resolved)*

`push`, `pop`, `map`, `filter`, `forEach`, `reduce`, etc. now dispatch
through `builtins/mod.rs::array_method_type`, which hands out a fresh
function type per lookup — polymorphic methods like `map`/`reduce` get a
fresh accumulator or result-element variable so each call site infers
independently.

The SPA's `deleteTodo`, `clearDone`, `countRemaining`, `hasAnyDone`,
`renderList`, and all the per-item handler factories collapsed from
loop-based to one-liners (`state.todos.filter(t => t.id !== id)` etc.).

`find` is typed `(T => Boolean) => T` — inty has no union types, so
"not found" at runtime returns `undefined` regardless of the declared
type. Same trade-off `getElementById` makes.

### 11. No arrow functions *(resolved)*

`(x) => x + 1`, `x => x + 1`, `() => body`, and `{ ... }` block bodies
all parse now. The parser lowers arrows to `Expr::Function` with
`name: None`, so inference/decoration/printing are unchanged.

Not modelled: `this` binding. Arrow functions in JS inherit the
enclosing `this`; inty's function handler re-creates a fresh `this`
variable for every function regardless. The SPA happens not to care.

### 12. No `let` *(resolved)*

`let` now parses as an alias for `var`. Per-block scoping and the
temporal-dead-zone aren't modelled (a `let` inside a `for` still shares
one binding across iterations for inference purposes) but the statement
parses and the types fall out correctly.

## Open gaps

### 3. No way to say "might be null"

There are no union types and no optional properties, so there's no way
to type `getElementById: (String) => Element | Null`. The shipped DOM
library pretends `getElementById` always succeeds. At runtime this is
fine for IDs we control, but it means inty cannot catch typos like
`getElementById("todo-lsit")`.

Related: `arr.find(...)`, `obj[missingKey]`, `JSON.parse` of arbitrary
input, any "not found" sentinel at all. This is the one gap that genuinely
needs a type-system extension (unions, options, or an explicit `?T` sugar).

### 7. `String` and `String[]` collide under structural indexing

A function that only uses `s.length` and `s[i]` satisfies both `String`
and `String[]` identically, so inty picks one by unification order
and may default wrongly. The workaround is to throw a `"" + s` into the
body to trigger the `Plus` type-class and pin it to `String`. Now that
`String.prototype` methods dispatch directly (gap 5), most real code
touches at least one string-specific method and the ambiguity never
fires — but a pure `length`/`[i]` function still has the problem.

### 8. Generic row-polymorphic helpers "forget" fields

A polymorphic helper `function removeById(arr, id)` is inferred at
`<a, b>({id: b | a}[], b) => {id: b | a}[]`, but when called with a
concrete todo array the returned element's `text` field comes back as
a free type variable rather than `String`. The workaround is to inline
the helper (lose the generic). Needs attention in the inference engine.

### 9. Control-flow-dependent return typing is strict

Any non-trailing branch that uses a bare `return;` forces the whole
function's return type to `Undefined`, and the trailing path must then
also return `undefined` explicitly. Handler bodies still need an explicit
`return undefined;` at the end (see `app.js` event handlers).

### 10. No ergonomic way to seed an empty typed collection *(resolved)*

An annotation on a `var`/`let`/`const` declaration with an initializer
works today — the annotation is parsed, unified with the initializer's
inferred type, and further operations are checked against the result:

```js
/** var todos: {id: Number, text: String, done: Boolean}[] */
var todos = [];

todos.push({id: 1, text: "hi", done: false});   // OK
todos.push({id: "bad", text: "hi", done: false}); // Type error
```

The SPA still seeds `state.todos` with two entries for illustrative
reasons, but the annotation form works and is now mentioned in the
comment above `state` so readers know the option is there.

### 13. No destructuring *(resolved, partial)*

Object and array destructuring in `var`/`let`/`const` declarations
parses and desugars to a sequence of simple declarators sharing a
synthesised temp binding. Covers:

```js
const {a, b: renamed} = obj;   // -> const $t = obj, a = $t.a, renamed = $t.b;
const [x, y] = tuple;          // -> const $t = tuple, x = $t[0], y = $t[1];
```

Not yet covered: nested patterns (`{a: {b}}`), defaults (`{a = 1}`),
rest (`{...xs}`, `[...tail]`), destructuring in function parameters,
destructuring in `for`-loop heads. Spread (`[...arr]`, `{...obj}`)
in expressions is also not done — needs more thought around typing
heterogeneous merges.

### 14a. No `class` *(resolved, partial)*

`class` declarations parse and desugar in the parser to factory
functions that return an object literal, matching the builder-pattern
style `test_builder_pattern.js` already exercises. Methods, a
constructor, and `new Class()` all work.

Class-body field declarations and access modifiers parse too:

```js
class Counter {
  private count: Number = 0;
  private name: String;
  constructor(name) { this.name = name; }
  inc() { return this.count + 1; }
}
```

Modifiers (`public` / `private` / `protected` / `readonly`) erase —
inty has no visibility model. Field annotations are accepted in
TS-style (`field: T`) and JSDoc-style (`/** field: T */`). A
declaration-only annotated field (no initializer, set in the
constructor body) moves its annotation to the constructor's
extracted property so the parameter is type-checked against the
declared type. Duplicate field declarations in the same class body
are rejected.

Not yet covered: `extends`/`super` (would need a prototype chain),
static methods, getters/setters in class bodies, private fields,
and constructor statements beyond `this.FIELD = EXPR;`.

### 14b. No `async`/`await` *(resolved)*

`Promise<T>` is a new parameterised nominal type alongside
`Array<T>` and `Map<T>`. `async function foo(x) { ... return e; }`
parses and desugars in the parser to
`function foo(x) { return Promise.resolve((function() { ... return e; })()); }`,
which types `foo` at `(T) => Promise<U>` with no new inference
rules. `await e` is a unary operator whose type rule is "expect
`Promise<T>`, produce `T`". `.then` / `.catch` / `.finally`
dispatch as built-in methods on `Promise<T>` with fresh inner
type variables per lookup. `fetch`, `Promise.resolve`,
`Promise.reject`, `Promise.all` all ship in the stdlib.

Trade-off forced by no-unions: `.then`'s callback must return
`Promise<U>`, not `U | Promise<U>` like in JS. Passing a bare
value errors with "expected Promise<a>, found Number"; users
wrap with `Promise.resolve(x)` or make the callback itself
`async`. The most common pattern is to chain `async` functions,
so the cost is low in practice.

Not enforced: `await` currently type-checks anywhere, not just
inside `async function`. That's a parser-level concern (requires
tracking "in async context") and doesn't affect soundness of
the types produced.

## What's left in priority order

1. **Nullability** (gap 3) — the remaining open gap that blocks idioms
   like `getElementById` safety, `find` results, and `JSON.parse`. Needs
   a type-system extension (unions, options, or a `?T` sugar).
2. **`async`/`await`** (gap 14b) — needs a `Promise<T>` built-in plus
   parser arms for `async` / `await`; the rest falls out of existing
   generics. No other blocker.
3. **Destructuring, round 2** (gap 13 continued) — nesting, defaults,
   rest/spread, patterns in function parameters. All pure parser work.
4. **Inference polish** (gaps 7, 8, 9) — smaller scope but each one
   removes a footgun.
5. **Class extras** (gap 14a continued) — `extends`, static methods,
   getters/setters.

## Additions beyond the original list

These weren't in the original 14 but got addressed alongside:

- **Inline `/*: T */` annotations** — scanner now captures them after
  the most recently emitted identifier, alongside the existing
  `/** var x: T */` doc-comment form. The form shown in `declare.md`
  finally matches what the tool does.
- **More Math / Object / Array static methods** — log/log2/log10, exp,
  all trig and hyperbolic functions, trunc, sign, hypot, LN2/LN10/
  LOG2E/LOG10E/SQRT2. Also `Object.keys` and `Array.isArray` as
  polymorphic declarations so each call site instantiates fresh.
- **ES6 module resolution** — `import "./foo.js"` and
  `import { a, b as c } from "./foo.js"` now resolve relative to the
  importing file, parse the target, infer it recursively, and merge
  the exported bindings into the env. Cycles error out explicitly.
- **`Promise<T>` / `async` / `await`** — new built-in parameterised
  nominal type (same shape as `Array<T>`). `async function` desugars
  to an IIFE wrapped in `Promise.resolve`; `await e` is a unary
  operator that unwraps `Promise<T>` to `T`. `fetch` in the stdlib
  returns `Promise<Response>`.
- **`.d.js` emit from a checked module** — `inty declarations
  <entry.js>` walks the module's effective export table and prints
  one `/** const NAME: T */ const NAME;` line per export. Internal
  bindings are omitted; re-exports flatten into inline schemes.
  Replaces `oxc`'s `IsolatedDeclarations` pass for downstream tools
  that publish a plugin's public surface. Programmatic API:
  `inty::declarations::emit_declarations(&CheckedModule)`.
- **Optional chaining (`?.`) and nullish coalescing (`??`)** — the
  parser builds a single `OptionalChain { head, segments }` AST node
  for chains containing at least one `?.`, so `a?.b.c` types as
  `T_c | Undefined` rather than erroring on the inner `.b` against
  a nullable. `??` is a dedicated `NullishCoalesce` node; result is
  `(T \ {Null, Undefined}) ∪ typeof RHS`. Non-nullable receivers
  type identically to `.` — `o?.name` on a non-null `o` produces
  just the field type, no `Undefined` widening. Idiomatic
  `arr.find(p)?.field ?? default` pulls a clean `T`.
- **Per-field type annotations on object literals** — the inline
  `/*: T */` form now also attaches to object property keys:
  `{ foo /*: Number */: 1, bar /*: String */: "" }`. The annotation
  is unified with the value's inferred type and the property is
  bound at the annotated type. Makes typed-empty-collection seeding
  in a state object readable:
  ```js
  let state = {
      todos  /*: Todo[] */: [],
      nextId /*: Number */: 1,
      filter /*: String */: "all"
  };
  ```

## SPA features used

The example in `app.js` ended up demonstrating every feature above.
What to look at for each:

| Feature | Where in `app.js` |
|---|---|
| Inline annotation with typed empty seed | `let state /*: {...} */ = {todos: [], ...}` at the top |
| Arrow functions | every event handler and `filter`/`map`/`forEach` callback |
| `let` / `const` | everywhere |
| String methods | `escapeHtml` (`.replaceAll` chain) |
| Array methods | `countRemaining`, `hasAnyDone`, `deleteTodo`, `clearDone`, `renderList` |
| Object destructuring | `renderTodoItem` (`const {id, text, done} = todo`) and the per-todo handler factory |
| Function hoisting | every handler closes over `render()`, which is defined at the bottom |
| Template literals | HTML string building throughout |
| Async / await / Promise | `persistTodos` and `save` for the Save button |
| Stdlib DOM + JSON | `document.getElementById`, `JSON.stringify` |

Modules aren't used in the main SPA because Chromium blocks
`type="module"` imports from `file://` URLs, which would make the
example stop running without a local HTTP server. A minimal
multi-file project demonstrating import/export lives in
`examples/modules/` — type-check with
`inty examples/modules/app.js`.

## By design (not going to fix)

A handful of JavaScript features are deliberately outside the scope
of inty. Marking them explicitly so they don't keep showing up
as "open" on the gap list.

**Prototype chain and anything that rides on it.** inty has no
inheritance model. Classes lower to factory functions returning an
object literal; that literal has no `__proto__`, no constructor
link, no dynamic dispatch through `prototype`. Consequently:

 * `class Child extends Parent` — no way to express "Child's
   instance is also a Parent-shaped thing" without subtyping, which
   we don't have.
 * `super(...)` / `super.method()` — same root.
 * `static` class members — modelling `Foo.bar` requires
   function-with-properties (a function value that also carries a
   row of static fields). We reject `static` at parse time with a
   pointer here.
 * `Object.prototype` / `Array.prototype` patching — user code
   can't walk prototypes because there aren't any to walk.
 * Private fields (`#foo`) — tied to class identity, which doesn't
   exist.
 * Instance-of checks (`instanceof`) — the operator parses but
   always types as Boolean; there's no real check.

**Dynamic `this` semantics.** A function's `this` is a fresh type
variable in the current inference rule, the same for every call.
So:

 * Arrow functions don't inherit enclosing `this` distinctly from
   regular functions (both currently get a fresh `this` variable).
 * `.call` / `.apply` / `.bind` to rebind `this` isn't type-checked.
 * Method detachment (`let f = obj.method; f()`) loses the `this`
   binding at runtime; inty doesn't warn because it has no
   notion of "bound to a receiver".

**`let` per-iteration binding and the temporal-dead-zone.** `let`
parses and lowers to the same AST node as `var`; inty treats
both as block-scoped for the purposes of where the name is visible
but doesn't model per-iteration bindings in a `for (let i ...)`
loop or the TDZ where referring to a `let` before its declaration
throws. These are runtime semantics irrelevant to types the way
inty uses them.

**`var` being function-scoped, not block-scoped.** `var` inside a
nested block is visible outside that block at runtime; inty
treats it as block-scoped, which is an over-approximation — the
false positives it produces are strict-but-sound.

If any of these become interesting enough to reconsider, the
minimum additions required are listed above: nominal class types
for inheritance, function-with-properties for static members,
`this`-aware inference for arrow rebinding.
