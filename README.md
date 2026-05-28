# inty

Inty is a static type checker with full type inference. Source code you check
with inty is just plain source in its surface language — no transpilation, no
added syntax — and runs as-is in the corresponding runtime.

Inty's inference engine is language-agnostic: a frontend lowers its surface
syntax onto a shared AST, and the type checker works on that AST.

Frontends:

- **JavaScript** — the primary frontend. Vanilla JS, optional JSDoc-style annotations.
- **Python** — a deliberately limited subset that lowers cleanly onto the type system.
- **Lua** — early sketch; the frontend parses a small subset, but it's not shipped end-to-end (no playground, no LSP integration).

The type system was designed to cover the common ground of these languages,
while deliberately leaving out parts that are "too dynamic", or considered
generally harmful.

inty is available as a CLI, an LSP server, and a WASM library.

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

Class inheritance (`extends`, `super`) and `static` class members are
deliberately out of scope — see [examples/spa/gaps.md § "By design"](examples/spa/gaps.md).
The only structurally useful thing they unlock is library-specific
instance-shape derivation (Stimulus-style `static targets` ↦ `this.fooTarget`),
which is closer to TypeScript's mapped types than to row polymorphism and is
also out of scope.

Open: making `&&` / `||` flow-narrowing-aware so default-value patterns like
`name || "Guest"` work without forcing operands' types to match. The
principal-typing property would need a careful rule.

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
