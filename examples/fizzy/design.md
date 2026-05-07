# inty — clean end-state design

The set of changes that, if landed, give inty principled support for the
JS idioms surfaced by the fizzy analysis. Distilled from the discussion
around `findings.md` and `plan.md`. Phases and migration order are
deliberately omitted — this is the destination, not the route.

Items already shipped in commit `1db1331` are listed under "Done"; the
rest is the open design.

## Type system

### Callable rows

Functions are rows with a reserved `<CALL>` field. `Type::Func(...)`
remains as the call signature inside the row; top-level callable values
always go through `Type::Row`. A plain function is `Row{<CALL>: F}`; a
constructor with statics is `Row{<CALL>: F, fromCharCode: G, …}`.

The call rule peeks `<CALL>` on the resolved callee. Free variables
unify with `(args) => ret` as today (preserving principal typing); rows
that have `<CALL>` peel it. The `Func ↔ Row{<CALL>}` direction in the
unifier handles `arr.map(String)` via plain row polymorphism — no
special coercion rule.

Subsumes: constructor statics (`String.fromCharCode`),
function-with-properties idioms, `arr.map(String)`,
`static` class members.

`.d.js` syntax: TS-style keyless call signature.
```javascript
/** const String: { (a) => String, fromCharCode: (Number) => String } */
const String;
```

### Nullable as union sugar

`T?` desugars to `T | Null | Undefined` at the annotation level. No new
nominal type. Reuses existing union machinery — control-flow joins,
narrowing through `=== null` / `=== undefined` / `typeof`, union
elimination on member access. `?.` and `??` become typing rules over
unions.

Subsumes: `getElementById`, `arr.find`, `JSON.parse`, `?.`, `??` flow
narrowing, optional fields on rows.

## Parser

### ASI

Insert a semicolon-equivalent before `return` / `break` / `continue` /
`throw` / postfix `++` / `--` when a line terminator precedes the next
token. Lexer already preserves newline info; parser needs a
`had_line_terminator_before(pos)` check at those four sites.

### Reject `delete`

Structured parse-time error pointing at the row-literal-omission
workaround. Closes the silent unsoundness without forcing
row-subtraction in the type system.

### Private fields `#x`

Lower at parse time to sentinel-keyed row storage. Each `#x` access
inside a class body rewrites to `this["<priv:Cls:x>"]` (or
`other["<priv:Cls:x>"]` for cross-instance reads). The sentinel name
contains characters JS source can't emit, so external access is
impossible from user code; access from inside the class is automatic
because the parser does the rewrite.

Per-class sentinel suffix prevents accidental collision when two
unrelated classes both use `#x`.

### `get foo()` / `set foo(v)` as opt-in method-mediation

First-class accessor declarations in class and object-literal bodies.
Lower to method-mediated row entries; reads of `obj.foo` recognize the
getter and type at its return type. Plain non-computed fields stay
direct on the row — method-mediation is opt-in, not the default
lowering.

## Module resolution

### `inty.json` with `paths` / `baseUrl`

tsconfig-paths-style alias resolver. Plus a stub-package convention
(`./inty-stubs/<spec>.d.js`) for bare specifiers. No type-system change;
just makes `import { Controller } from "@hotwired/stimulus"` resolvable
once the user supplies a `.d.js` stub.

## Stdlib

### Primitive constructors as callable rows

Migrate `String`, `Number`, `Boolean` from Rust `initial_env()` bindings
to `core.d.js` callable-row declarations. Adds the static methods
(`String.fromCharCode`, `Number.isInteger`, etc.) without losing
constructor callability.

### DOM expansion

Continue filling out Element / Document / Window / Navigator with
faithful, non-self-recursive shapes (using `T` placeholders where
self-reference would otherwise be needed). Most of this is already
done; remaining work is adding fields as user code surfaces them.

### `Date`

Single pragmatic constructor signature plus the prototype methods.
Loses overload distinction; users with multi-arity construction wrap in
a small typed helper.

## Out of scope by design

These are deliberate omissions. Each has been considered and rejected
either because it requires a structural type-system extension we don't
want to defend forever, or because it's a runtime semantic outside the
type checker's scope.

- `class extends`, `super`, nominal class identity.
- Stimulus-style mapped-types-style derivation from class-static literals.
- Intersection types (rows are merged via row-poly instead).
- `any` / `unknown` (already rejected with diagnostic).
- Overloaded function signatures (one principal type per binding).
- Equirecursive types in annotations (μ-types). Internal equirecursive
  inference for `return this` chains stays — but `.d.js` authors keep
  using `T` placeholders for self-referential shapes.
- Arrow `this` binding distinct from regular function `this`.
- Per-iteration `let`, TDZ, `var` function-scoping.

## Done

Items in commit `1db1331` (Phase 0–2 of the earlier `plan.md`):

- `export function` peer hoisting fixed.
- `export async function` parses.
- `export default class` parses (existing inheritance rejection still
  fires with a gaps.md pointer).
- Default parameter values, destructuring defaults, rest parameters,
  spread in call arguments, `catch {}` without binding,
  object property shorthand.
- Stdlib expansion: `Object.{values,entries,assign,fromEntries}`,
  `Array.{from,of}`, `atob`, `btoa`, `navigator`, `AbortController`,
  `FormData`, `URLSearchParams`, `TextDecoder`, `TextEncoder`,
  `CustomEvent`, `Event`, `customElements`, `visualViewport`,
  `getComputedStyle`, `requestAnimationFrame`,
  `cancelAnimationFrame`, ~80-field Element shape, `Regex.test/exec`
  method dispatch.

These ship; the design above is what comes next.
