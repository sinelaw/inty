# Changelog

## Unreleased

### JavaScript the parser and stdlib take

- `export class Name { … }` (and `export class Name;` for an external
  class).
- `from`, `of` and `as` are contextual keywords, names everywhere else:
  `const from = 1` is a binding.
- Array patterns take holes: `const [a, , c] = t`, `[, b] = t`.
- `async` methods, in classes and object literals; an async function's
  body keeps its `this` (the `Promise.resolve` lifting now uses an arrow).
- A class member may be named by a keyword (`delete(k)`, `default()`),
  as an object literal's may.
- Class methods and constructors take default and destructuring
  parameters, as plain functions do; a whole destructured parameter takes
  a default (`function f({a} = {a: 1})`).
- A constructor may run statements besides `this.f = …`: each runs where
  it stands, between the fields set before and after it, and may read
  those set before as `this.f`. A field is still set only by a
  `this.f = …` line of the constructor's own; a `return`, and a name the
  constructor declares that a method also reads, are rejected.
- Stdlib: `new Promise((resolve, reject) => …)`; `EventSource`;
  `XMLHttpRequest.open(method, url, async?, user?, password?)`; a regex's
  `lastIndex` takes a store (`re.lastIndex = 0`).

### Fixes from moving Rosaclef to 276dd1f

- An object-literal field's `/** @type {T} */` annotation checks its
  initialiser, as a `const`'s does: `/** @type {() => Undefined} */ mark:
  null` is an error ("expected '() => Undefined', found 'Null'"), where it
  was accepted and `hooks.mark()` threw. A field that starts as `null` is
  declared `T | Null`. (The `null` / `undefined` placeholder rule is gone.)
- An importer of a module that failed no longer reports errors in its own,
  correct code ("Property 'bank' not found in type Boolean", "expected
  'Boolean | Undefined', found '{pattern: …}'"). The failed module's names
  are typed `Error`; a type variable that met one stayed free and was
  pinned by its first use. It is now `Error` too: unifying with `Error`,
  indexing an `Error` value, a constraint on one and a spread of one all
  give `Error`.
- A binding written once after its initialiser, by a plain `x = e` in its
  own function, is narrowed after that write: the get-or-create idiom
  (`let x = m.get(k); if (!x) { x = []; m.set(k, x); } x.push(1);`) and
  the `exec` loop (`while (m) { …m[1]…; m = re.exec(s); }`) type-check
  without a `const` copy. See
  [docs/flow-narrowing-safe.md](docs/flow-narrowing-safe.md), "Extension:
  bindings written once".
- A tested property read again (`if (o.f) o.f()`) is still not narrowed:
  a getter can give a different value to each read, and a type doesn't say
  which fields are getters. Copy it into a `const` and test that.

### Multi-line annotations

Long type annotations can be written across lines, nicely laid out, and mean
exactly what they mean on one line (see
[docs/type-system.md](docs/type-system.md#long-annotations-across-lines)):

```javascript
/** type ScoreView = {
 *   id: String,
 *   fitWidth: Number,  // the width the page is laid out for
 *   engraveMs: Number, // how long the last engraving took
 * } */

/** function sideView(
 *   b: Builder,
 *   v: ScoreView,
 * ) => Undefined */
```

- A JSDoc `*` margin at the start of each line after the first is ignored, in
  `type`, `function`, `const`/`let`/`var` and `class` annotations, with the
  keyword on the first line or on the line after `/**`. With the keyword
  after a margin, the comment is an annotation only if its type parses;
  otherwise it is prose (`/**\n * function foo(bar) is deprecated …`), as
  before.
- `//` comments to the end of a line are allowed inside an annotation and
  ignored by the checker.
- Trailing commas are accepted after the last parameter of a function type,
  type argument, type parameter and tuple element (object fields already
  accepted one), and a union may start with `|`.
- Errors inside an annotation are reported at the offending name or
  character, on its own line, instead of across the whole comment. This
  moves the reported position of existing annotation errors (unknown type,
  wrong number of type arguments, rank-1 restriction, required parameter
  after an optional one) from the comment's start to the culprit.
- New `inty fmt [--check] [--width=N] <file | dir>...`: rewrites each one-line
  annotation longer than the width (default 100) one field, parameter or
  union member per line, with a `*` margin and a trailing comma. Short and
  already multi-line annotations, and all code, are left as they are, so it
  is idempotent. A rewrite is kept only if it parses to the same types as
  the original.

One-line annotations check exactly as before. Two edge cases of malformed
annotations change: a doc comment that starts like an annotation but stops
early (`/** const a: A, (b) */`) is now skipped whole instead of having its
leftover text read as code, and an unterminated `/** type …` is now an
unterminated-comment error.

### Fixes

- `/** const a: …, b: … */` no longer splits a declarator at a comma inside a
  string literal type (`"a, b"`) or after an arrow inside type arguments
  (`Pair<() => A, B>`).
- An empty comment `/**/` ends at its own `*/`. It used to be read as the
  start of a doc comment running to the next `*/`, swallowing the code in
  between.
