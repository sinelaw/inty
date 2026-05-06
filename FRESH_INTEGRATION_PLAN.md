# Fresh integration plan

Plan for the work needed in `inty` so the `fresh` editor can drop its
`oxc` dependency and use `inty` exclusively for type‑checking and
bundling its plugin system.

Branch: `claude/inty-fresh-integration-zZzai` (off `master`).
Shape: **single PR** containing all items, stacked as separate
commits on `claude/inty-fresh-integration-zZzai` so individual
pieces stay reviewable.

## Order and effort

| # | Item | Effort | Status |
|---|------|--------|--------|
| P2 | `.d.js` emit from a checked module | S (~½ day) | **done** |
| P4 | Class field declarations + modifier tolerance | S–M (~1 day) | **done** |
| P7 | Optional chaining `?.` and nullish coalescing `??` | M (~1–2 days) | **done** |
| P3 | Spread/rest in object & array literals + destructuring rest | M–L (~2 days) | **done** |
| P1 | Bundler crate `inty-bundle` + CLI `inty bundle` | L (~2–3 days) | **done** |
| P6 | User‑defined generic type aliases | L (~2–3 days) | **done** |
| P8 | TS‑flavor parser + pretty printer + `.d.ts` loader | M–L (~2 days) | planned |
| ~~P5~~ | ~~Discriminated‑union narrowing on tag fields~~ | — | **deferred — don't do** |

Rationale for the order:

- P2 first: pure read‑side, no typing rules. Warm‑up that exercises
  the export‑iteration plumbing P1 also needs.
- P4 next: parser‑only, unblocks migration sources.
- P7 before P3 because `?.`/`??` is contained; P3 changes row
  unification.
- P1 after P3 so the bundler doesn't have to special‑case spread.
- P6 before P8 so generic aliases exist on the inty side before TS
  surface is added.
- P5 is the highest type‑system risk and is deferred.

## Cross‑cutting

- All items land on a single PR against `master` from
  `claude/inty-fresh-integration-zZzai`. Each item is its own
  commit (or small commit series) with a clear subject so the PR
  is reviewable item‑by‑item.
- Each item's commit updates `examples/spa/gaps.md` with the same
  resolved/open/out‑of‑scope classification it already uses.
- Tests: add to existing layout (`infer/tests.rs`, parser tests,
  `tests/metamorphic.rs` where applicable). Prefer end‑to‑end (parse
  + check + assert types) over white‑box.
- Diagnostics: every new error path includes a span and a
  user‑actionable message; match tone of existing diagnostics.
  **For every rejected TS construct (P8) the diagnostic must
  suggest the inty alternative idiom** — see the rejection table
  in P8.
- Typing‑rule additions (P3, P7) each land catalog entry +
  dynamics arm so `meta::blame` and `meta::soundness` keep passing.
- Don't break `examples/spa/app.js` or any stdlib file.
- No new crate dependencies beyond what's in `Cargo.toml` without
  justification (P1 is the legitimate exception; see below).

## Decisions

- **PR shape**: single PR on `claude/inty-fresh-integration-zZzai`
  against `master`, items as separate commits.
- **Source maps**: use the `sourcemap` crate. Added to
  `crates/inty-bundle/Cargo.toml` as a runtime dep.
- **Bundler runtime test**: use `quickjs-rs` (or `rquickjs`) as a
  dev‑dep on `crates/inty-bundle/`. Round‑trip
  `examples/spa/app.js` through the bundler and execute the result
  to assert the same final state as today.

---

## P2 — `.d.js` emit from a checked module

Replaces `oxc`'s `IsolatedDeclarations` pass. `fresh` uses it to
publish each plugin's public surface so other plugins can import it.

### Behaviour

- Walk the module's export table; for each export, look up its
  inferred type and format as a stdlib‑style declaration line.
- Emit `/** const NAME: T */` (or `function …`) declarations.
- Internal (non‑exported) bindings must NOT appear.

### Public API

```rust
pub fn emit_declarations(module: &CheckedModule) -> String;
```

### CLI

`inty declarations <entry.js>` prints to stdout.

### Tests

Take `examples/spa/app.js`, emit its `.d.js`, parse it back through
inty as a stdlib lib (`--lib`), and confirm the resulting type
environment matches what the original module exported.

### Files touched

- New module under `crates/inty/src/` (e.g. `declarations.rs`).
- Reuse `types/pretty.rs` and `modules.rs` export tables.
- `crates/inty-cli/` for the new subcommand.

---

## P4 — Class field declarations + modifier tolerance

Migration sources use TS‑style class‑body field declarations:

```ts
class Foo {
  private name: string;
  private items: Item[] = [];
  private count = 0;
  constructor(name) { this.name = name; }
  add(item) { this.items.push(item); }
}
```

### Behaviour

- Parser accepts and erases `public`/`private`/`protected` —
  no semantic effect under inty's structural typing.
- Parser accepts class‑body field declarations. Each field becomes
  equivalent to an assignment at the start of the constructor body.
- Initializers execute in field‑declaration order, before user code
  in the constructor.
- Fields without initializers are `this.foo = undefined` AT TYPE
  LEVEL — the row includes the field with the annotated type, or a
  fresh variable if unannotated.
- Annotation form: `field: T` (TS‑style) OR `field /** : T */`
  (JSDoc‑style). Accept both.

### Out of scope (still rejected)

`static`, `extends`, `super`, `#private` fields. Existing diagnostics
keep firing.

### Tests

Rewrite an existing class example to use field declarations and
modifiers; confirm same inferred types. Parser tests for each form.

### Files touched

- `crates/inty/src/parser/mod.rs` — class body parsing.
- Possibly `crates/inty/src/lexer/` for TS‑style annotation tokens
  if not already accepted.

---

## P7 — Optional chaining (`?.`) and nullish coalescing (`??`)

### Strategy

Dedicated AST nodes + two small typing rules + catalog/dynamics arms.
A pure parser desugar to `cond ? undefined : a.b` does NOT preserve
the typing the spec demands (four distinct breakages: pollutes
non‑nullable receivers with `Undefined`; fails field access on
nullable receivers before narrowing fires; leaks `Null` back into
`??` results; chains require narrowing through synthesized temps).

### Typing rules

- `a?.b` (and `a?.()`, `a?.[k]`): if `a : T | Null | Undefined`,
  result is `T_b | Undefined` where `T_b` is the type of the access
  against the non‑null branch. If `a` isn't nullable, no `Undefined`
  is introduced.
- `a ?? b`: if `a : T | Null | Undefined`, result is
  `(T \ {Null, Undefined}) ∪ typeof b`. If `a` isn't nullable, `b`
  must still type‑check but the result is just `T`.

### Parser

- New tokens `?.` and `??` in the lexer (with the TC39 disambiguation
  rule: `?.` doesn't lex when the next char is a digit, so
  `cond ? .5 : 0` still works).
- `??` precedence below `||`.
- `?.` at member‑access precedence; whole chain represented as a
  single `OptionalChain { head, segments }` node so `a?.b.c` types
  as `T_c | Undefined` rather than re‑evaluating short‑circuit at
  each segment.

### Catalog + dynamics

- Catalog arms for both ops in `operators/mod.rs`.
- Dynamics in `dynamics/step.rs`. `?.` may itself reduce via
  `cond ? undefined : a.b` at the dynamics level (only the typing
  has to be direct). `??` reduces by checking nullish on the LHS
  value and selecting LHS or RHS without re‑evaluating LHS.
- Soundness probe additions: nullish/non‑nullish LHS variants for
  both ops.

### Tests

- Parser tests: each form parses (`a?.b`, `a?.()`, `a?.[i]`,
  `a ?? b`, chained, mixed).
- Inference tests in `infer/tests.rs`: nullable receiver →
  `T | Undefined`; non‑nullable receiver → `T`; `??` between
  `String | Null` and `String` → `String`; chains.
- End‑to‑end: `arr.find(p)?.field ?? default` type‑checks cleanly
  (the exact migration pattern).

---

## P3 — Spread/rest in object and array literals

### Object spread (row polymorphism)

`{ ...a, ...b }` produces a row that is the right‑biased merge of
`a`'s and `b`'s rows. Repeated keys take the rightmost type. The
result row's tail is the tail of the last spread operand if it's a
row variable.

### Array spread

`[...xs, y]` requires `xs : T[]` and `y : T`, producing `T[]`. Mixing
element types fails as it does today for plain array literals.

### Rest in destructuring

- `const { a, ...rest } = obj` binds `rest` to the row formed by
  removing `a` from `obj`'s row.
- `const [head, ...tail] = xs` gives `tail : T[]`.

### Tests

Cover each form with end‑to‑end inference tests. Include
options‑row construction `{ ...defaults, key: value }`, config
merging in class constructors, array concatenation `[...xs, y]`.
Update `examples/spa/gaps.md`.

### Files touched

- Parser arms for spread/rest in object and array literals and in
  destructuring patterns.
- `infer/features/rows.rs` — row merge with right‑bias and tail
  handling, "row minus field" operation.
- `operators/mod.rs` and `dynamics/step.rs` — catalog + reduction.

---

## P1 — Bundler crate `inty-bundle`

Build a bundler that takes an entry `.js` file and produces a single
JS blob that QuickJS can `eval`, with all imports resolved inline.
Reuse the module graph from `crates/inty/src/modules.rs`. Runs AFTER
successful type checking.

### Output shape

- Each module wrapped in an IIFE that returns its export table.
- `import { x, y as z } from "./foo.js"` rewritten to local
  references against the importing module's IIFE scope.
- `import * as ns from "./foo.js"` rewritten to a namespace object.
- `import name from "./foo.js"` rewrites to that module's `default`.
- `export … from "./foo.js"` re‑exports flatten into the importer's
  export table.
- Top‑level statements in the entry module run at eval time.
- Side‑effect‑only `import "./foo.js"` runs `foo`'s top‑level
  statements once, in dependency order.

### Cycles

Detect import cycles and reject with a clear diagnostic in v1. Don't
ship silently broken cycles.

### Source maps

Emit a v3 JSON source map alongside the bundle, mapping each output
line/column back to the originating file and span. Inty already
tracks spans in its parser AST; thread them through.

### Public API (sketch)

```rust
pub fn bundle(entry: &Path) -> Result<BundleOutput, BundleError>;
pub struct BundleOutput {
    pub code: String,
    pub source_map: String,
}
```

### CLI

`inty bundle <entry.js> [-o out.js]`. With `-o`, also write
`<out>.js.map`. Default to stdout.

### Tests

- Round‑trip `examples/spa/app.js` through the bundler. Run through
  QuickJS (or shape‑compare; see open decisions). The output must
  execute to the same final DOM state as today.
- Unit tests for: re‑exports, namespace imports, default exports,
  side‑effect imports, cycle rejection.

### Files touched

- New crate `crates/inty-bundle/` added to workspace.
- `crates/inty-cli/` for `inty bundle` subcommand.
- `crates/inty/src/modules.rs` if any plumbing is missing for span
  threading.

---

## P6 — User‑defined generic type aliases

Today inty supports type parameters in built‑in/stdlib annotations
(`Promise<T>`, `Array<T>`). Allow the same in user code.

### Syntax (sketch)

```js
/** type Cancellable<T> = { result: Promise<T>, cancel: () => Promise<Boolean> } */
/** type Subscription   = { unsubscribe: () => Undefined } */
```

### Resolution

When a type alias is referenced (`Cancellable<HoverResp>`),
substitute the type argument(s) for the parameter(s) in the alias
body, then proceed as if the user had written the substituted form
inline.

### Identity

Aliases are NOT nominal — `Cancellable<X>` and the equivalent inline
row are interchangeable. Don't emit "type X is not assignable to
Cancellable<X>" diagnostics.

### Recursive aliases

Allow only via a clear cycle through a row, e.g.
`type Tree<T> = { value: T, children: Tree<T>[] }`. Equi‑recursive
unfolding already exists for inferred types — extend it to alias
references.

### Files touched

- `crates/inty/src/infer/type_parser.rs` — alias declarations and
  references.
- `crates/inty/src/infer/state.rs` — alias environment alongside
  the type env.
- `crates/inty/src/types/ty.rs` — alias‑reference type or inline
  substitution.
- Pretty printer round‑trip.

---

## P8 — TS‑flavor parser + pretty printer + `.d.ts` loader

Lets `fresh` import `.d.ts` files directly and write annotations
in the TS syntax that's already common in the migration sources.
Output: `inty declarations` can emit `.d.ts` instead of `.d.js`.

### What maps cleanly (accept)

- Primitives: `string`/`number`/`boolean`/`null`/`undefined` ↔
  `String`/`Number`/`Boolean`/`Null`/`Undefined`. `void` →
  `Undefined`.
- Arrays: `T[]` and `Array<T>`.
- Object/record: `{ x: number; y: string }` ↔ closed rows.
  Semicolons or commas, both legal.
- Function types: `(x: T, y: U) => R`. Rest params slot in once
  P3 lands.
- Unions: `A | B`. String‑literal unions `"a" | "b"`.
- Built‑in generics: `Promise<T>`, `Map<K, V>`. After P6, user
  generics `Foo<T>`.
- `interface Foo { ... }` ↔ row type alias (after P6,
  `interface Foo<T>`).
- `type Foo<T> = ...` — same as P6 alias with TS surface.
- Optional property `x?: T` ↔ `x: T | Undefined`. Same for
  optional params `(x?: T) =>`.
- `readonly` — accept and erase.
- Top‑level `declare const/function/class` in `.d.ts`.
- `export` / `export default` / `export { … }` in `.d.ts`.

### What gets rejected (with a clear diagnostic + suggested alternative)

Every rejected construct emits a span‑anchored diagnostic that
names the construct AND points at the inty idiom that replaces it.
Tone matches existing diagnostics ("Help: ..." trailing line).

| Rejected TS construct | Suggested inty idiom |
|---|---|
| `any` | use a concrete type, or a closed union of the values you actually accept |
| `unknown` | same as `any` — the parser cannot model "any value" without subtyping |
| `never` | omit the return type; an unreachable function infers fine, or use `Undefined` |
| `void` | use `Undefined` (the migration target). `void` is accepted at return positions only as a synonym |
| intersection `A & B` | merge the rows into a single object type `{ ...fields of A, ...fields of B }` |
| `keyof T` | enumerate the keys as a string‑literal union: `"a" \| "b" \| "c"` |
| `typeof v` (in type position) | name the type explicitly; inty has no value‑to‑type reflection |
| indexed access `T[K]` | name the field's type directly |
| mapped types `{ [K in keys]: T }` | write the row out, or wrap in a generic alias `type Foo<T> = { ... }` (P6) |
| conditional types `T extends U ? X : Y` | split into two named aliases or two function overloads at use sites |
| tuple types `[T, U]` | use a record `{ first: T, second: U }` — inty has no tuples |
| type assertion `as T` | annotate the binding instead: `/** const x: T */` |
| `extends` on type parameter | drop the constraint; inty's row polymorphism does the bounded work structurally |
| `namespace` / module declarations | use ES modules with `export`/`import` |
| `///` triple‑slash references | use `--lib` on the CLI or import the `.d.ts` directly |
| declaration merging (multiple `interface Foo`) | combine into a single `interface Foo` |
| `static` class members | move to a top‑level `const` outside the class |
| `#private` fields | use a regular field; inty has no class identity to gate on |
| function overloads | merge into one signature with a union parameter type |

### Three sub‑capabilities

1. **TS syntax in JSDoc and inline annotations — per‑file flavor,
   no auto‑detect.** Type parser at `infer/type_parser.rs` learns a
   TS dialect alongside the current one. Flavor is selected
   per‑file by:
   - File extension: `.ts` and `.d.ts` files are TS‑flavor by
     default (no marker needed).
   - Explicit marker: a leading `// @inty-format: ts` (or `inty`)
     line at the very top of the file forces flavor regardless of
     extension.
   - Default for everything else (`.js`, `.d.js`): inty‑flavor.

   No comment‑level or expression‑level mixing: ambiguous cases
   like `{x: T}` would tiebreak silently and that's exactly what
   the no‑auto‑detect rule prevents. Within a single file, all
   annotations parse in the same flavor.
2. **`.d.ts` loader.** Parser entry that reads top‑level
   `declare …`, `interface …`, `type …`, `export …` and produces
   the same `CheckedModule` shape the existing stdlib loader does.
   `inty --lib path/to/foo.d.ts` Just Works (the `.d.ts` extension
   selects TS flavor automatically). Unsupported constructs reject
   with span and the alternative‑idiom suggestion from the table
   above.
3. **TS‑flavor pretty printer.** Second formatter (in or alongside
   `types/pretty.rs`) emitting `{ x: number; y: string }` style.
   Wired to `--format=ts|inty` on `inty declarations` (P2) and
   `--annotate`. Format `ts` emits `.d.ts` (file extension and
   syntax both).

### Tests

- Round‑trip `fresh`'s editor‑API stub (or a representative slice)
  through the loader; type‑check a small program against it; re‑emit
  and diff.
- Meta round‑trip: inty → TS → inty asserts type identity, parallel
  to existing meta‑checks.

### Risks

- `.d.ts` files in the wild use `keyof`/intersection/overloads.
  Diagnostics must point at the rejected construct, not the whole
  file.
- Two pretty printers means two places to keep in sync as
  `types/ty.rs` grows. The round‑trip meta‑test is what catches
  drift.

---

## Deferred

### P5 — Discriminated‑union narrowing on tag fields

**Deferred — don't do** in this batch. Highest type‑system risk and
narrowing on bare bindings (`typeof x === "..."`, `x === literal`)
already exists; extending to path‑based refinement on `x.tag` plus
switch and early‑return integration is its own design pass.

If reconsidered: implement narrowing for `if (x.tag === "literal")
{ … } else { … }` (both branches), `===` and `!==` only, switch
statements where each case narrows, and early‑return form
`if (x.tag !== "a") return; …` narrowing the tail. Discriminator
must be a row field whose inferred type is a string‑literal union.
String‑literal tags only — no numeric, no structural.
