# inty

Inty is a static type checker with full type inference. Source code you check
with inty is just plain source in its surface language — no transpilation, no
added syntax — and runs as-is in the corresponding runtime.

Inty is an alternative to TypeScript.

Inty's inference engine is language-agnostic: a frontend lowers its surface
syntax onto a shared AST, and the type checker works on that AST.

Frontends:

- **JavaScript** - the primary frontend. You write vanilla JS, with optional JSDoc-style annotations, and inty type checks it for you.

And also:

- **Python** - *experimental* a deliberately limited subset that lowers cleanly onto the type system.
- **Lua** - *experimental* early sketch; the frontend parses a small subset, but it's not shipped end-to-end (no playground, no LSP integration).

The type system was designed to cover JavaScript's "good parts" and the common ground of these languages,
while deliberately leaving out parts that are too dynamic, or considered
generally harmful.

inty is available as a CLI, an LSP server, and a WASM library.

There is also an experimental Go backend. `inty go file.js` translates a
fully type-checked program into Go, to show what the static types are
worth at runtime. See [examples/go-backend](examples/go-backend/README.md)
and the [benchmarks against Node and Bun](examples/go-backend/BENCHMARKS.md).

**Formal model (work in progress).** A model of a core of inty's type
system in Lean 4 has machine-checked proofs that well-typed programs don't
get stuck, and that its type inference is sound and complete. Tests run
inty, the model and Node on the same programs and compare the results. The
model doesn't cover all of inty yet. See [lean/README.md](lean/README.md)
for what is proved, and [lean/ROADMAP.md](lean/ROADMAP.md) for what is
left.

Try it online at: https://sinelaw.github.io/inty/

inty is based on [infernu](https://github.com/sinelaw/infernu).

## Usage

Build the CLI (which also ships the LSP server):

```sh
cargo build --release -p inty-cli
# binary lands at target/release/inty
```

Check a file:

```sh
inty path/to/file.js
inty path/to/file.py
```

The frontend is picked from the file extension. Run `inty --help` for the full
set of options.

The LSP server is included as a CLI command (`inty lsp`). A minimal VS Code
adapter lives in [`editors/vscode/`](editors/vscode/) — run
[`editors/vscode/install.sh`](editors/vscode/install.sh) to build, package, and
install it in one step.

## How does it compare to TypeScript?

|                    | TypeScript                           | **Inty**                                                |
| ------------------ | ------------------------------------ | ------------------------------------------------------- |
| **Build step**     | Transpiles to JavaScript             | A pure type checker — no transpilation, vanilla source  |
| **Relation to source** | A superset (sometimes) of JavaScript | A subset of the source language, deliberately discarding the "bad parts" |
| **Typing style**   | Gradual typing, requires annotations | Strictly full static typing, type inference, annotations are optional |

There is no `any` type in inty. `null`/`undefined` are explicit via union types.

## Strict by Design

inty isn't a strict mode you opt into — it's the only mode. Every variable,
expression, and function return has a single type for its lifetime. The type
may be polymorphic, or a closed union of literals or row shapes, but it can't
*change* under assignment, and operators that combine values still require
their operands' types to agree. The benefit is that type errors become
compile-time errors, with no runtime fallback.

## JavaScript idioms, the inty way

For JavaScript programmers, and for people coming from typed languages who
want to write JavaScript with inty. Your code stays plain JavaScript: inty
infers types, and where you need to state one it goes in a comment
(`/** let x: T */`, `/** function f(a: A) => R */`). The rule to keep in
mind is that each variable has one type for its whole life, so the idioms
below are mostly about saying "this may be missing" or "this is one of
several types" explicitly. More in [docs/patterns.md](docs/patterns.md) and
[docs/type-system.md](docs/type-system.md).

**A function that may return nothing.** Declare the optional type, return
`undefined` explicitly, and unwrap at the call site.

```js
/** function find(xs: Number[], v: Number) => Number? */   // Number? = Number | Undefined
function find(xs, v) { for (const x of xs) { if (x === v) return x; } return undefined; }
const n = find([1, 2], 2) ?? 0;
```

Unannotated, `if (c) return 1; return null;` is an error (inty doesn't guess
the union). A conditional with an `undefined` or `null` arm is fine:
`xs.length > 0 ? xs[0] : undefined`.

**Checking a property for null.** Copy it into a `const` and test that;
`if (o.p !== null) o.p + 1` doesn't type-check.

```js
const p = o.p;
if (p !== null) p + 1;
```

**A variable that holds different types.** Declare the union; `let id = 1;
id = "abc";` is an error.

```js
/** let id: Number | String */
let id = 1;
id = "abc";
```

**An empty array filled later.** Give it its element type.

```js
/** let names: String[] */
let names = [];
names.push("a");
```

**An object used as a map.** Make it a `Dict`; reads give `V | Undefined`.
A record can't be read with a key known only at run time (`o[k]`).

```js
/** const counts: Dict<Number> */
const counts = {};
counts[w] = (counts[w] ?? 0) + 1;
```

**Objects of several shapes.** A tagged union, taken apart by testing the tag.

```js
/** type Shape = {kind: "circle", r: Number} | {kind: "rect", w: Number, h: Number} */
/** function area(s: Shape) => Number */
function area(s) { return s.kind === "circle" ? 3.14 * s.r * s.r : s.w * s.h; }
```

**Building strings from numbers.** `"n=" + 3` is an error; convert
explicitly.

```js
`n=${n}`;   "n=" + String(n);   n.toFixed(2);
```

**Default values.** `??` on an optional parameter.

```js
/** function greet(name: String?) => String */
function greet(name) { return "hi " + (name ?? "guest"); }
```

**Iterating.** `for…of` and spread work on arrays, strings, `Set` and `Map`.

```js
for (const [k, v] of new Map([["a", 1]])) {}
for (const c of "abc") {}
const xs = [...new Set([1, 2])];
const squares = Array.from({ length: 5 }, (_, i) => i * i);
```

**DOM lookups.** `getElementById` may return `null`; test it first.

```js
const btn = document.getElementById("go");
if (btn) btn.addEventListener("click", (e) => e.preventDefault());
```

## Type system

The type system features — full inference, parametric and row polymorphism,
type classes, equi-recursive types for method chains, callable rows, union
types and predicate refinement, class bodies with private fields, ES modules
— along with the JavaScript syntax accepted, the rejected idioms, and the
annotation grammar, are documented separately:

- [docs/type-system.md](docs/type-system.md) — features, examples, accepted/rejected syntax, annotation grammar.
- [modules.md](modules.md) — module resolution design (and `examples/modules/` for runnable fixtures).
- [docs/jsdoc-at-type.md](docs/jsdoc-at-type.md) — `@type {T}` and `typeof` rules.

## Future Work

`static` class members are deliberately out of scope — see
[examples/spa/gaps.md § "By design"](examples/spa/gaps.md). The only
structurally useful thing they unlock is library-specific instance-shape
derivation (Stimulus-style `static targets` ↦ `this.fooTarget`), which is
closer to TypeScript's mapped types than to row polymorphism. Class
inheritance (`extends`) is not supported, except in the declaration of an
external class without a body (`/** class X extends B { … } */ class X;`),
and neither are setters; getters, field initialisers (which read through
`this` only fields set before them) and `new` are, see
[docs/type-system.md](docs/type-system.md#class-bodies-fields-private-fields-accessors).

Open: polymorphic record fields (rank-2), and one-event-per-name DOM typing,
which needs them — see [docs/design-notes.md](docs/design-notes.md).

## Using inty on a real project

[docs/patterns.md](docs/patterns.md) collects the patterns a real ~6k-line
vanilla-JS application (Rosaclef) settled on — typed FFI boundaries, brand
newtypes, dictionaries — and which workarounds are no longer needed.
[docs/performance.md](docs/performance.md) describes how checking scales
(`inty --timings`, checking several files in one run), and
[docs/rosaclef-report.md](docs/rosaclef-report.md) the fixes that project's
report led to.

## Self-testing

inty is heavily tested against itself: every operator's typing rule is
cross-checked against an operational semantics, and a property test generates
well-typed programs by construction and reduces them to verify they never get
"stuck". See [ARCHITECTURE.md](ARCHITECTURE.md) for the module layout and the
four test layers.

## Background

inty is based on the type system developed for
[infernu](https://github.com/sinelaw/infernu). See [infernu.md](infernu.md) for
a partial formalization. The implementation also covers `this` resolution,
Rank-1 restrictions on type annotations, and a value restriction for
generalisation and polymorphic-property mutation; the formal document doesn't
go into these.

The JavaScript inty checks is just JavaScript and runs in browsers, server
runtimes, or even embedded engines. See
[mquickjs](https://github.com/bellard/mquickjs), a runtime that also supports a
subset of JavaScript.
