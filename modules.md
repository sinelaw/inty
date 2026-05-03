# minfern — module support

This document is a design proposal. It catalogues what `import`/`export` already
does in minfern, walks the [MDN `import`
reference](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Statements/import)
form by form, and proposes how to close the gaps. Implementation is staged so
each step is independently shippable.

## What works today

`src/modules.rs` implements a file-based resolver. From an entry file the
pipeline is:

1. Parse the entry program (`src/parser/mod.rs` parses every `import` form
   into `Stmt::Import { specifiers, source, span }`).
2. For each `Stmt::Import`, resolve `source` relative to the importing file's
   directory, trying the literal path then `.js` then `.d.js`
   (`resolve_path` in `src/modules.rs`).
3. Recursively `parse → resolve_imports → infer` the target, then build an
   **explicit export table** by walking the program's `Stmt::Export` nodes
   (`collect_exports` in `src/modules.rs`). The table is a `Vec<{exported,
   local}>`; the resolver looks up the requested name in the table, takes
   the local binding it points to, and reads its scheme out of the inferred
   env. Bindings without an `export` clause are invisible — that is the
   single source of truth for module visibility.
4. Cycle detection via a `HashSet<PathBuf>` of canonicalised paths.
5. Type inference treats `Stmt::Export` as a transparent wrapper around the
   underlying declaration so locals get bound normally; `ExportDecl::List`
   is purely a visibility marker and only validates that each `local` is
   declared.

The currently supported surface:

| Form                                              | Status |
|---------------------------------------------------|--------|
| `import "./foo.js";`                              | ✅ side-effect: merges every export under its exported name |
| `import { a } from "./foo.js";`                   | ✅      |
| `import { a as b } from "./foo.js";`              | ✅      |
| `import { a, b, c } from "./foo.js";`             | ✅      |
| `import foo from "./mod.js";`                     | ✅      |
| `import foo, { a } from "./mod.js";`              | ✅ (composes from default + named) |
| `export var x = …;` / `export let x = …;`         | ✅      |
| `export const x = …;`                             | ✅      |
| `export function f(…) { … }`                      | ✅      |
| `export default …;`                               | ✅ (expression or named function) |
| `export { a, b as c };`                           | ✅      |
| `import * as ns from "./mod.js";`                 | ✅ namespace as `Type::Module` (per-export polymorphism preserved) |
| `import foo, * as ns from "./mod.js";`            | ✅ default + namespace (composes §1 + §2) |
| `export { a, b as c } from "./mod.js";`           | ✅ named re-export, with renaming |
| `export { default } from "./mod.js";`             | ✅ re-export target's default as ours |
| `export { default as alias } from "./mod.js";`    | ✅ |
| `export * from "./mod.js";`                       | ✅ all named exports (excludes `default`, per ESM) |
| `export * as ns from "./mod.js";`                 | ✅ target's namespace as one export |
| `import "lodash";` (bare specifier)               | ❌ resolver looks for a file path only |
| `await import("./mod.js")` (dynamic)              | ❌ no expression form |
| `import x from "./d.json" with { type: "json" };` | ❌ no attributes |

The two `⚠️` rows are noteworthy: the parser accepts the syntax but
`resolve_imports` returns `"default imports are not supported"` /
`"namespace imports are not supported"` (`src/modules.rs:88`,
`src/modules.rs:96`). Filling those in is the smallest possible first step.

## Goals and non-goals

**Goals.**

- Cover every form on the MDN `import` reference page that has a sound
  static-typing story under HMF.
- Each missing form lands as a single PR touching the parser, the resolver,
  and one test fixture under `examples/modules/`.
- Cross-module inference stays principal: the module's exported scheme is
  the same one that local references would have seen.

**Non-goals.**

- Live ES-module semantics (live bindings, TDZ across modules, top-level
  `await`). minfern uses an evaluation-on-load model and that is fine for
  the static type system.
- Tree-shaking, bundling, source maps. The resolver is a checker, not a
  builder.
- Node `package.json` resolution. Bare specifiers route through a small
  registry (see §6) rather than re-implementing Node's algorithm.

## 1. Default imports / default exports

MDN: `import name from "module";` and `export default expr;` (or
`export default function …`, `export default class …`).

**Design.** Treat `default` as a reserved export name. Concretely:

- Parser: add `Stmt::Export { declaration: ExportDecl::Default { value, span } }`
  with three flavours (`Expr`, `Function`, `Class`) for the three RHS forms.
  No new tokens — `default` is already `Token::Default` (`src/lexer/token.rs:65`).
- Inference: `ExportDecl::Default` introduces a fresh local binding called
  `default` in the module's env. For `export default function f()` the
  binding is also visible under `f` inside the module, matching JS.
- Resolver: `ImportSpecifier::Default { local }` looks up `default` in the
  module env and re-binds under `local`. Drop the `not supported` error.

Value-restriction policy is unchanged — `export default` of a non-value
behaves exactly like `const default = …;`. Anonymous `export default function
() {}` synthesises a name to keep error messages legible.

## 2. Namespace imports

MDN: `import * as ns from "module";`

**Status: shipped.** Implemented as a dedicated `Type::Module { source,
exports: BTreeMap<String, TypeScheme> }` variant rather than a row, after
weighing three options (modules-as-rows with row-generalization,
`RowField::Scheme`, and a first-class module type). The dedicated variant
won on robustness:

- *Polymorphism is intrinsic.* Each export is stored as its own
  `TypeScheme`; member access goes through `infer_member_on_type` ⇒
  `state.instantiate(&scheme)` so each `ns.foo` re-instantiates per use.
  No row-generalization trick, no shared quantifier scope, no dependency
  on `instantiate` not leaking constraints. The metamorphic-style proof
  is the test `namespace_preserves_polymorphism_across_uses`: with
  `export function id(x) { return x; }`, both `ns.id(1)` and
  `ns.id("hello")` type-check in the same program.
- *Mutability is wrong-by-construction.* Modules carry no field-assignment
  rule, so `ns.foo = bar` simply doesn't type-check — the type system
  *can't express* mutating a namespace. Rows would have allowed it.
- *Identity is nominal by source.* `Type::Module` unifies with itself iff
  `source` matches (the canonicalised file path). Two imports of the same
  file produce the same type; two imports of different files don't unify
  even if their export shapes coincide. This matches ESM semantics: each
  module is its own thing.
- *Diagnostics carry the source.* `ns.bogus` produces "module
  `"./identity.js"` has no export named `"bogus"`" rather than a generic
  "row missing property bogus", because `infer_member` knows it's looking
  at a module.

Cost: a `Type::Module` arm in every site that walks `Type` —
`Subst::apply`, `Type::collect_free_vars`, `unify`, `pretty`,
`infer_member_on_type`, `infer_member_from_type`, `occurs_in`. Mechanical;
no algorithmic novelty. The remaining match sites (`narrow`, `decorate`,
`type_parser` structural-equality, `find_origin_in_type`) all have
default arms and treat modules as opaque, which is the right semantic.

Future: §4 (re-exports) builds another `ModuleType` from the imported
module's exports; §7 (dynamic `import()`) returns `Promise<Type::Module>`;
§9 (cross-module type-class instances) hangs instance metadata off the
`ModuleType`. The variant is the carrier the rest of the design wants.

## 3. Export lists and renamed exports

MDN: `export { name1, name2 as alias };` and `export { default as alias };`
(without a `from`).

**Design.** New `ExportDecl::List { specifiers: Vec<ExportSpecifier> }`,
where each specifier is `{ local, exported, span }`. Inference for an
`ExportDecl::List` is a no-op on types (the locals are already bound) but
records an export map. To keep the existing resolver model — "diff the env
to find the exports" — we add an explicit `exports: HashMap<String, String>`
collected during inference and threaded through `infer_program_with_env`.
The resolver consults the map before falling back to the diff.

## 4. Re-exports

MDN:

- `export { name } from "./mod.js";`
- `export * from "./mod.js";`
- `export * as ns from "./mod.js";`
- `export { default } from "./mod.js";`

**Status: shipped.** Parsed as `ExportDecl::From { kind, source, span }`
with `ExportFromKind::Named(Vec<ExportSpecifier>) | All | AllAs(String)`.
Inference is a no-op — re-exports introduce no local bindings.

The resolver work pivots on the `ExportEntry`:

```rust
pub enum ExportBinding {
    Local(String),       // existing: name in this module's TypeEnv
    Inline(TypeScheme),  // new: scheme already extracted from elsewhere
}
```

`Local` is what `export const x = …` and `export { foo as bar };` produce
— the entry points back at this module's env. `Inline` is what
`export … from` produces — the scheme has already been pulled from the
target module, so no second lookup is needed (and no need to extend this
module's `TypeEnv` with phantom bindings).

`compute_export_table` walks `Stmt::Export` after inference. For each
`ExportDecl::From` it:

1. Resolves the path; cycle-checks against the shared `visiting` set
   (so a re-export cycle errors with the same "circular" diagnostic as
   an import cycle).
2. Calls `load_module` on the target, getting back its
   `(TypeEnv, ExportTable)`.
3. Materialises entries based on the kind:
   - `Named`: for each spec, looks up `spec.local` in the target's
     export table, resolves to a scheme, pushes
     `Inline(scheme)` under `spec.exported`.
   - `All`: copies every entry whose `exported != "default"`. ESM
     intentionally excludes the target's default; the test
     `re_export_star_excludes_default` pins this.
   - `AllAs(ns)`: builds a `Type::Module` from the target via the same
     `build_namespace_type` helper §2 uses, wraps it in a mono scheme,
     pushes under `ns`.

Composition falls out: a chain `a.js → b.js → c.js` of `export { x } from`
re-exports works because each hop's `Inline` entry already carries the
fully-resolved scheme; no recursion at lookup time. `re_export_through_two_hops_works`
covers this. `default` re-exports work via `expect_module_name`'s
`Token::Default` handling on both sides of `as`.

## 5. Combined default + named / default + namespace

MDN: `import foo, { a, b } from "./mod.js";` and `import foo, * as ns
from "./mod.js";`

**Status: shipped.** Both forms now parse to one `Default` and one
`Named`/`Namespace` specifier in the same `Stmt::Import`; the resolver's
existing §1 / §2 paths each take their specifier with no new wiring.
The parser change was a single branch after the default-comma accepting
either `{` or `*`.

## 6. Bare specifiers

MDN: `import _ from "lodash";`

**Design.** Introduce a small registry `src/modules/registry.rs` mapping
bare specifier → resolved path or stdlib module identifier. Two sources
populate it:

- A built-in table for stdlib modules already documented in
  `missing-builtins.md`. Entries point into the `stdlib/` directory's
  `.d.js` declaration files.
- A user-supplied JSON file (`minfern.modules.json`) discovered by walking
  upwards from the entry file. Each entry maps `"name"` to a path.

`resolve_path` tries the registry before treating the specifier as a path,
so `./` and `../` keep their existing meaning. Bare specifiers without a
registry entry produce a structured error pointing at the import span.

We deliberately do not implement Node's `node_modules` resolution: minfern
is a checker, and silently picking up JS from `node_modules` is exactly the
kind of action whose blast radius warrants explicit configuration.

## 7. Dynamic `import()`

MDN: `await import("./mod.js");` returns a promise of the module namespace.

**Design.** Parse `import(expr)` as `Expr::DynamicImport { source, span }`.
Type-check by:

1. Requiring `source` to be a string literal at the call site (we have no
   way to type a runtime-computed path). Non-literal arguments produce a
   "dynamic import requires a string literal" error.
2. Resolving the literal exactly like a static import.
3. Returning `Promise<Namespace>` where `Namespace` is the row built in §2.

This restriction is documented at the error site; if a real use case
demands runtime paths we can revisit by introducing `any`-shaped namespace
types. For now we keep inference principal.

## 8. Import attributes

MDN: `import data from "./d.json" with { type: "json" };`

**Design.** Parse the `with { … }` clause into `Stmt::Import { …,
attributes: Vec<(String, String)> }`. The only attribute we recognise is
`type: "json"`, which switches `load_module` from "parse + infer JS" to
"parse JSON, infer its type as a closed object literal, expose under the
default export." Anything else is a structured error citing the unknown
attribute.

JSON support is a real win — `examples/modules/` could ship a
`config.json` and load it without hand-writing a `.d.js` shim.

## 9. Cross-module type-class instances

The catalog in `src/classes/` is a process-global table. Today a module
that adds an instance silently affects every later-checked module, which
is fine because instances are declared by the stdlib only. If a user
module ever exports an instance it should be explicit:

```
export class Plus instance for MyVec;
```

This is not on the MDN page but it falls out of the module work — design
it now so we don't paint ourselves into a corner. Proposed: instances are
exported by name like any other binding, the registry merges them when the
import is resolved, and conflicting instances at the merge point are an
error. Mark this as deferred until §1–§7 are in.

## Test plan

Each step lands with:

- A unit test in `src/modules.rs`'s `mod tests` covering the happy path
  and one failure.
- A fixture under `examples/modules/` exercising the new form end-to-end.
  `examples/modules/app.js` is the canonical entry — extend it to consume
  whatever new form is being added (default import, namespace import, …).
- A metamorphic test where applicable: `import x from "./m.js"` followed
  by an alpha-rename of `x` should keep the inferred type identical, and
  the existing `t_alpha_rename_existing` transformation
  (`tests/metamorphic.rs`) generalises to imports for free once the
  resolver knows about them.

A blame-style test does *not* fit module support — there is no operator
catalog row to enumerate. The dynamics module deliberately doesn't see
imports either; cross-module evaluation is out of scope for the
operational semantics.

## Suggested ordering

1. **§1 default imports/exports** — smallest diff, unblocks the largest
   fraction of real-world code.
2. **§3 export lists and renamed exports** — pure parser + inference work;
   no resolver changes beyond the new exports map.
3. **§2 namespace imports** — needs the row-of-schemes change; touches
   `src/types/`.
4. **§5 combined forms** — falls out for free once §1+§2 land.
5. **§4 re-exports** — re-uses the resolver, no new types.
6. **§6 bare specifiers** — registry plumbing; touches the CLI.
7. **§7 dynamic import** — new expression node, new type form.
8. **§8 import attributes** — JSON loader.
9. **§9 type-class instance exports** — only after §1–§7 are stable.

Each step is independently mergeable, each leaves the existing examples
green, and each grows `examples/modules/` by one file so the user-visible
surface keeps pace with what the checker accepts.

## Current state

§1, §2, §3, §4, §5 are landed and exercised by fixtures under
`examples/modules/`. The remaining MDN-shaped work is §6 (bare
specifiers), §7 (dynamic `import()`), §8 (import attributes), and §9
(cross-module type-class instances), each independent and orderable
per the section above.

## Open issues to address before §6+ land

These don't block any of the remaining sections but they're real bugs
or papercuts in what's already shipped. A future contributor picking up
the next section should consider clearing them first.

1. **Re-export error spans land in the wrong file.** When
   `compute_export_table` fails because a re-export target doesn't have
   the requested name (e.g. `export { ghost } from "./inner.js";` and
   `inner.js` has no `ghost`), the error bubbles up with the inner
   module's span attached to the *outer* module's import statement.
   The diagnostic message correctly names the offending module, but the
   highlighted source location can be a few files away from the
   `export … from` clause that caused the load. Wrap the
   `load_module(...)` call in `compute_export_table` to attach a
   "while resolving `export { … } from \"…\"`" frame so the
   highlighted span belongs to the re-export clause itself.

2. **`ns.foo = bar` is silently allowed.** `Type::Module` has no
   field-assignment rule — assignment falls through and tends to fail
   later as a unification mismatch instead of "cannot assign to module
   export". The right place to catch it is the `Expr::Member` arm of
   `check_assignment_target` in `src/infer/features/bindings.rs`; the
   TODO there already describes the fix. A test
   `assigning_to_namespace_field_errors` belongs in `modules.rs` once
   the check lands.

3. **Importer's env leaks into loaded modules.** `load_module` threads
   the caller's `starting_env` into `resolve_imports` for the target,
   so a module loaded mid-chain sees whatever bindings the importer
   happened to have. ESM modules are isolated. Fix: always start a
   target with `crate::builtins::initial_env()` (or a single shared
   immutable base), regardless of who's calling. Today nothing breaks
   because module bindings don't shadow stdlib names in practice, but
   it's a latent footgun.

4. **No module cache.** A diamond `main → a, main → b, a → c, b → c`
   re-parses, re-resolves, and re-infers `c.js` twice. `Type::Module`'s
   nominal-by-source identity means the two passes still unify
   correctly, but the work is wasted (linear in dependency-graph
   re-traversals). Add a `HashMap<PathBuf, (TypeEnv, ExportTable)>`
   keyed on the canonical path; `visiting` already gives the right
   key shape. Be careful that the cache is keyed on the *fully
   resolved* module — caching mid-resolution would tangle with cycle
   detection.

5. **Module subtyping is intentionally absent.** Documented on
   `ModuleType` in `src/types/ty.rs`. If a future use case demands
   structural module reuse (a function parameter typed as "any module
   exporting `greet`"), it should land as a row-typed parameter, not
   as a width-subtyping rule on `Type::Module` — module identity is
   nominal by source path and changing that would silently weaken
   diagnostics across the board.
