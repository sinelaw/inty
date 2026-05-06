# Plan: improving inty without changing the type system

Follow-up to `findings.md`. Goal of this plan: enumerate the concrete
improvements that the fizzy analysis surfaced, scoped to **parser, stdlib,
module resolver, diagnostics, tooling** — not the type system. Each item is a
discrete unit with a paste-able acceptance test, ordered into shippable
phases.

The planning premise is that the "by design" rejections in
`examples/spa/gaps.md` § "By design" stand. So no class inheritance, no
static class members, no private fields, no nullable types. Anything that
needs those is out of scope for this plan.

## Phase 0 — bug fixes (~half a day)

Two real bugs in inty surfaced by fizzy. Both are independent of the parser
work below and worth landing first so later changes don't get tangled with
them.

### 0.1 `export function` peer forward references don't hoist

**Symptom.** `export function a() { return b(); } export function b() {…}`
errors with `Undefined variable: 'b'`. Plain `function a/b` works; only the
exported form is broken.

**Root cause.** `crates/inty/src/infer/mod.rs:142` only collects
`Stmt::FunctionDecl` into the binding group. `Stmt::Export { declaration:
ExportDecl::Function, … }` (built by
`crates/inty/src/parser/mod.rs:597–620`) is a different AST node, so it
breaks the group.

**Fix sketch.** Extend the group predicate so a run of
`Stmt::FunctionDecl | Stmt::Export{ExportDecl::Function} | Stmt::Empty`
forms one group. `infer_function_group` then needs to know which entries
are exports so it can both bind them in the local env and emit them into
the module's exports table.

**Acceptance.**
```js
export function a(x) { return b(x); }
export function b(x) { return 1; }
```
type-checks; existing tests still pass; add the test in
`crates/inty/src/infer/tests.rs`.

### 0.2 `delete o.a` is silently unsound

**Symptom.** After `delete o.a`, reads of `o.a` still pass.

**Decision.** The cheapest correct behaviour, given inty has no nullable types,
is to **reject** `delete` at parse time with a diagnostic pointing at the
factory-function workaround, the same way `static` already does. Modelling
delete properly needs row subtraction on a value, which the type system
doesn't have.

**Fix.** Add an arm to the unary expression parser that errors on `delete`
with `expected: "expression (delete is not supported — construct a new
object literal omitting the field instead)"`.

**Acceptance.** `var o = {a: 1}; delete o.a;` now errors with a clear
message; the existing `delete` test (if any) is removed or rewritten.

## Phase 1 — parser additions (~one to two days total)

Each item is one parser arm or one lowering pass. They are independent and
can land in any order; group them however is convenient. All belong in
`crates/inty/src/parser/mod.rs` plus a few AST helpers.

### 1.1 `export async function f(){}`

**Where.** `parse_export_declaration`, the `Token::Function` arm
(`parser/mod.rs:597`). Add a peek for `Token::Async` before `Token::Function`
that sets `next_fn_is_async = true` and falls through.

**Acceptance.**
```js
export async function f(x) { return await Promise.resolve(x); }
```
infers `f: <a>(a) => Promise<a>`.

### 1.2 `export default class { … }` and `export default class extends X { … }`

**Where.** `parse_export_declaration`, the `Token::Default` arm. Currently
it expects an expression; a bare `class` keyword without a name fails
because `class` is parsed as a statement.

The class-extends form is rejected later in the class parser
(`parser/mod.rs:2719+`); leave that rejection in place but **point to
`examples/spa/gaps.md`**. The point of this item is that the parser should
get *past* the `export default` token, parse `class` as an anonymous class
expression, and only then surface the (existing) "no inheritance" error.

**Acceptance.** Both forms parse and produce the same anonymous-class
error as a non-exported `class extends X {}`. No silent acceptance of
inheritance.

### 1.3 Default parameter values

**Where.** `parse_parameters` at `parser/mod.rs:1360`. A parameter is
currently `expect_ident()`; extend to accept an optional `= expression`
suffix.

**Lowering.** Two options:
- (a) Lower at parse time to `if (param === undefined) param = default;`
  prepended to the function body.
- (b) Add an `Option<Expr>` default to `Param` and have inference do the
  unification with `param: T` and the default's type.

(a) is less code and reuses the existing `===`/narrowing path. Recommend (a).

**Acceptance.**
```js
function throttle(fn, delay = 1000) { return delay; }
function id(x = 0) { return x; }
```
both type-check; calling `throttle(fn)` infers `delay : Number`.

### 1.4 Destructuring defaults

**Where.** The destructuring lowering already lives in the parser. Extend
the object-pattern arm to accept `key = expr` and the array-pattern arm
to accept `ident = expr`.

**Lowering.** Same trick as 1.3 — synthesize `if (binding === undefined)
binding = default;` after the destructuring assignment. Already works
because destructuring lowers to plain `var` declarators.

**Acceptance.**
```js
function orient({ target, anchor = null, reset = false }) { return reset; }
const [head = 0, tail = 0] = [1];
```
both type-check.

### 1.5 Rest parameters

**Where.** `parse_parameters`. Accept a single `...ident` as the last
parameter; bind it as `T[]`.

**AST.** Either a flag on the last `Param` or an `Option<RestParam>` on the
function. Whichever is closer to the existing array-rest pattern; the
spread/rest in object/array literals already handled this kind of thing.

**Acceptance.**
```js
function f(...args) { return args; }
function g(first, ...rest) { return rest; }
const xs = f(1, 2, 3);     // xs : Number[]
const ys = g("a", "b", "c"); // ys : String[]
```

### 1.6 Spread in call arguments

**Where.** `parse_arguments` at `parser/mod.rs:2294`. A `...expr` argument
should desugar to a runtime apply, but for type purposes it suffices to
unify `expr : T[]` with the function's expected `T[]` rest parameter (paired
with 1.5).

**Acceptance.**
```js
const arr = [1, 2, 3];
const m = Math.max(...arr);              // m : Number
const s = String.fromCharCode(...arr);   // s : String
```

### 1.7 `catch {}` without binding

**Where.** Try/catch parser around `parser/mod.rs:1736`. Currently expects
`(`; allow `Token::LBrace` directly and bind the catch parameter to a
fresh hole.

**Acceptance.**
```js
async function f() { try { await Promise.resolve(1); } catch {} }
```

### 1.8 Class field with arrow-function initializer

**Where.** Class-body field parser around `parser/mod.rs:780+`. A field
initializer `= expression` already parses; the issue is when the initializer
is `async () => {…}` or `() => {…}`. Verify the existing path handles arrow
expressions and add a regression test if it doesn't.

**Acceptance.**
```js
class A { handler = () => 1; }
const a = new A();
const n = a.handler();  // n : Number
```
(Note: `#handler` itself stays out of scope per gaps.md "by design".)

### 1.9 Tagged template literals

**Where.** Primary expression parser. Currently `String.raw\`hi\`` parses
as a property access `.raw` followed by a separate template literal,
producing a wrong type. Recognize a template literal directly after a
member expression as a tagged template and lower to
`tag(strings, ...substitutions)` (or, more simply, a call where the
argument shape matches the template).

**Acceptance.**
```js
const s = String.raw`a${1}b`;  // s : String
```

## Phase 2 — stdlib expansion (~one day)

All `.d.js` edits, no Rust. Update `crates/inty/stdlib/core.d.js` and
`crates/inty/stdlib/dom.d.js`. Each addition is independent; size/effort is
mostly the work of writing accurate type signatures.

### 2.1 Globals missing entirely

| Binding              | Used by                                       | Notes                                                                   |
|----------------------|-----------------------------------------------|-------------------------------------------------------------------------|
| `Date`               | `helpers/date_helpers.js`                     | Constructor variants + `getFullYear`, `getMonth`, `getDate`, `getTime`, etc. |
| `navigator`          | `platform_helpers`, `badge_controller`, etc.  | `userAgent`, `maxTouchPoints`, `clipboard.writeText`, `setAppBadge`, `clearAppBadge`, `credentials.{create,get}` |
| `URLSearchParams`    | `lib/action_pack/passkey.js`                  | Constructor + `append`, `get`, `set`, `toString`                        |
| `FormData`           | `helpers/form_helpers.js`                     | `new FormData(form)`                                                    |
| `AbortController`    | `lib/action_pack/passkey.js`                  | `new AbortController()`, `.signal`, `.abort()`                          |
| `TextDecoder` / `TextEncoder` | `lib/action_pack/webauthn.js`        | `decode(buffer) : String`, `encode(s) : Uint8Array`                     |
| `Uint8Array`, `Int8Array`, `ArrayBuffer` | `webauthn.js`                | constructor, `.buffer`, `.length`, `Uint8Array.from(iter, fn)`          |
| `CustomEvent`, `Event` | many controllers                            | `new CustomEvent(name, { bubbles, detail })`                            |
| `customElements`     | `lib/action_pack/passkey.js`                  | `define(name, ctor)`                                                    |
| `atob` / `btoa`      | `webauthn.js`                                  | `(String) => String`                                                    |

### 2.2 DOM Element/Document/Window expansion

The current Element row is 11 fields. Real code reaches well past it. Add:

* **Events**: `addEventListener`, `removeEventListener`, `dispatchEvent`.
* **Attributes**: `setAttribute`, `getAttribute`, `hasAttribute`, `removeAttribute`,
  `toggleAttribute`, `dataset.*` (as a row of `String` fields).
* **Selectors**: `querySelector`, `querySelectorAll`, `closest`, `matches`,
  `contains`.
* **Tree**: `cloneNode`, `before`, `after`, `append`, `prepend`, `remove`,
  `replaceWith`, `parentElement`, `children`, `firstElementChild`,
  `lastElementChild`, `nextElementSibling`, `previousElementSibling`.
* **Geometry / scroll**: `getBoundingClientRect`, `scrollIntoView`, `scrollTop`,
  `scrollLeft`, `scrollWidth`, `scrollHeight`, `offsetWidth`, `offsetHeight`,
  `offsetTop`, `offsetLeft`.
* **Form**: `submit`, `requestSubmit`, `reset`, `checkValidity`,
  `reportValidity`, `disabled`, `value`, `valueAsNumber`, `checked`, `name`,
  `form`.
* **Focus / state**: `focus`, `blur`, `autofocus`, `hidden`, `loading`,
  `tabIndex`.
* **classList** as a row: `{ add, remove, toggle, contains, replace }`.

`window` needs `location` (incl. mutations), `scrollX/Y/innerWidth/innerHeight`,
`visualViewport`, `addEventListener`, `dispatchEvent`, plus user mutability of
`window.X` for app globals.

`document` needs `head`, `body`, `documentElement`, `activeElement`,
`querySelector`/`querySelectorAll`/`getElementById`/`createElement`/
`createDocumentFragment` returning the expanded Element shape.

**Acceptance.** Pick three specific files: `helpers/html_helpers.js`,
`controllers/auto_click_controller.js`, `controllers/copy_to_clipboard_controller.js`.
After the parser items above and this item, those three should type-check.

### 2.3 Static-method coverage

| Static                | Use site                                       |
|-----------------------|------------------------------------------------|
| `Date.now()`          | timing helpers                                 |
| `Object.assign`       | row-merge alternative to `{...a, ...b}`        |
| `Object.entries`      | iterate object as `[key, value]` pairs         |
| `Object.values`       | iterate object values                          |
| `Object.fromEntries`  | reverse of above                               |
| `Array.from`          | `Array.from(NodeList).forEach(...)` is common  |
| `Array.of`            | typed empty array seeding                      |
| `String.fromCharCode` | `webauthn.js`                                  |
| `String.raw`          | needs item 1.9 to be useful                    |
| `Number.isInteger`, `Number.isFinite`, `Number.isNaN` | minor             |

### 2.4 `Regex.test/match/exec`

The `Regex` nominal type exists but its method dispatch isn't wired.
Either declare them in `core.d.js` (if Regex can be typed as a row) or add
to `crates/inty/src/builtins/mod.rs` next to the array/string-method
dispatch.

**Acceptance.**
```js
/\d+/.test("abc 123");   // : Boolean
"hello".match(/l+/);     // : { 0: String, index: Number, input: String } | Null
```
(the `Null` half stays open until nullable types ship; for now type as a
non-null row and document the unsoundness.)

## Phase 3 — module resolver (~one day)

### 3.1 Path-alias / import-root config

**Why.** Fizzy uses Rails importmap. Imports like `import "controllers"` and
`import { isMobile } from "helpers/platform_helpers"` resolve via the
importmap config, not relatively. inty currently rejects them.

**Design.**
- Add an optional `inty.json` (or `[inty]` section in `package.json`,
  pick one) with a `paths` map and a `baseUrl` field, mirroring tsconfig.
- The resolver in `crates/inty/src/modules.rs` checks aliases before
  falling back to relative resolution.
- The bundler (`crates/inty-bundle`) already rejects bare specifiers; once
  aliases resolve them, the bundler should accept the resolved path.

**Acceptance.** A minimal fixture with
```jsonc
// inty.json
{ "baseUrl": "./app/javascript", "paths": { "controllers/*": ["./controllers/*"] } }
```
and a file using `import { application } from "controllers/application"`
type-checks.

### 3.2 Stub-package mechanism for bare specifiers

**Why.** `import { Controller } from "@hotwired/stimulus"` is a third-party
import. inty has no `node_modules` story.

**Design.** Two equivalent options:
- Treat bare specifiers as additional `paths` entries with a default of
  `./node_modules/<spec>/<spec>.d.js`.
- Add a `stubs` directory convention (`./inty-stubs/@hotwired/stimulus.d.js`)
  searched after the user's local files but before erroring.

Either way, the user is responsible for hand-writing the `.d.js`. inty's job
is just to find it.

**Acceptance.** A user-supplied `inty-stubs/@hotwired/stimulus.d.js` declaring
`Controller` as an opaque type makes `import { Controller } from
"@hotwired/stimulus"` resolve. (Whether `class extends Controller` then
checks is a separate type-system question, out of scope.)

## Phase 4 — diagnostics polish (~half a day)

The "by design" rejections produce confusing errors right now if the user
hasn't read `gaps.md`. Each rejection should point to the workaround.

### 4.1 Extend "see examples/spa/gaps.md" diagnostic to all by-design rejections

The `static` arm already does this. Replicate for:

* `class … extends X` (parser/mod.rs class-extends arm).
* `super` calls / member access.
* `#field` and `#method` (currently a generic "Unexpected character: '#'";
  should be a structured "private fields are not supported — see gaps.md
  for the closure-captured-`let` workaround").
* `instanceof` (currently parses but always types as Boolean — at minimum
  warn; ideally reject with a pointer to the discriminator-field pattern).
* `delete o.a` (per item 0.2).

### 4.2 `--explain` for type-class errors

`Plus a` and `Indexable a` errors are inty's most idiomatic and least
intuitive. Add `inty --explain plus` / `--explain indexable` (or numeric
codes like rustc) that prints the type-class definition, the instances, and
worked examples.

**Acceptance.** Running `inty --explain plus` prints a one-page note
covering what `Plus` is, why string and number are separate instances, and
the canonical workaround (`String(n)` or template literals).

## Phase 5 — tooling / DX (~one to two days)

### 5.1 Watch mode

`inty check --watch <entry.js>` re-runs on file change. Use `notify` crate.
Re-uses the existing checker; the savings come from not re-loading and
re-parsing the embedded stdlib on every invocation.

### 5.2 LSP improvements

- **Incremental rechecking.** Currently the LSP probably reparses on every
  keystroke. Cache parsed modules keyed on (path, mtime, content hash) and
  only re-infer the changed module + its dependents.
- **Go-to-definition across modules.** The module graph is already built
  during inference; expose it to the LSP layer.
- **Rename.** Symbol renames within a module are straightforward given the
  AST + spans.
- **Completion** is bigger. Skip for this plan.

### 5.3 `inty init`

Generate a minimal `inty.json` (item 3.1) in the current directory based
on the detected layout: if `app/javascript/` exists treat as Rails-ish, if
`src/` exists treat as plain.

## Sequencing and dependencies

```
Phase 0 (bug fixes) ──────────┐
                              ▼
Phase 1 (parser) ─────► Phase 2 (stdlib) ─────┐
                              │                ▼
                              ▼          Phase 4 (diagnostics)
                        Phase 3 (resolver)
                              │
                              ▼
                        Phase 5 (tooling)
```

* Phase 0 first to keep later changes uncomplicated.
* Phase 1 and Phase 2 are mostly orthogonal but Phase 1 unblocks more
  programs per day of work, so start there.
* Phase 3 only matters once Phase 1 + 2 are done — without those, no
  third-party-imported code parses anyway.
* Phase 4 and Phase 5 are quality polish; safe to defer.

## Acceptance criteria for the plan as a whole

After Phases 0–3:

* All 9 files in `app/javascript/helpers/` of fizzy type-check.
* The 5 initializers type-check, except the parts using `class` with
  private methods.
* `lib/action_pack/webauthn.js` type-checks.
* `lib/action_pack/passkey.js` and the 65 controllers still don't —
  they need inheritance (out of scope per gaps.md "by design").
* The fizzy-reachable LOC under inty grows from ~0% to roughly 12%
  (helpers + webauthn + initializers, ~520 LOC of 4 114).

That number caps low because the type-system limits dominate. The
parser/stdlib/resolver work is still high-leverage for non-Stimulus
real-world JS, where inheritance is much less common than fizzy's case.

## Out of scope (explicitly)

These belong to a different plan:

* Class inheritance, `super`, static class members, private fields,
  `instanceof` semantics — `examples/spa/gaps.md` § "By design".
* Nullable / option types — gaps.md § 3, the largest open type-system gap.
* TypeScript-mapped-types-style derivation needed to type Stimulus's
  dynamic accessors — `findings.md` § F.
* Arrow-function `this` inheritance, `let` per-iteration binding, TDZ —
  gaps.md § "By design".

If any of these become priorities later, they should be planned separately;
none of the work in Phases 0–5 should foreclose those options.
