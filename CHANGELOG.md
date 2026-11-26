# Changelog

## Unreleased

### Starlark, and Python lowerings

- A Starlark frontend (`.star`, `.bzl`, `.sky`), a mode of the Python
  one. It rejects what Starlark leaves out of Python (`class`, `try`,
  `raise`, `while`, `import`, `global`, `with`, decorators, `is`, `**`,
  f-strings) and checks Starlark's static rules: no `if`/`for` at the top
  level, a global is bound once, and no recursion. `load("//pkg:f.bzl",
  "name", local = "name")` loads typed names from another file, resolving
  the label against the workspace root (`MODULE.bazel`, `WORKSPACE`,
  `.buckconfig`, …) or the loading file's package; a label in another
  repository (`@repo//…`) binds its names unchecked. `fail(…)` is a
  `throw`, and `struct(a = 1)` a record. A `.bzl` file sees Bazel's
  globals (`rule`, `attr`, `native`, `provider`, `depset`, …), accepted
  without checking until they are declared. The CLI and the language
  server pick it from the extension.
- Python: list comprehensions (several `for`/`if` clauses, tuple
  targets), and a generator expression as the sole argument of a call that
  iterates it (`any`, `all`, `sum`, `sorted`, `join`, …).
- Python: slices `xs[a:b:c]` of lists and strings.
- Python: keyword-only parameters (`def f(a, *, b)`).
- Python: PEP 484 type comments, `x = []  # type: list[str]` and
  `# type: (int, str) -> bool` after a `def` header (a method's may leave
  out `self`).
- Python: a `dict[str, V]`'s methods (`get`, `keys`, `values`, `items`,
  `pop`, `popitem`, `setdefault`, `update`, `clear`, `copy`), and
  iterating it gives its keys. `d.get(k)` is `V | None`; `d.get(k, default)`
  is `V` when `d` is known to be a dict at the call.
- Python: `str.partition`, `str.rpartition` and `str.isascii`.
- Starlark is its own language to inference (`SourceLanguage::Starlark`,
  typed by the Python rules): a string isn't iterable (`s.elems()` is),
  and `str`, `list` and `dict` have Starlark's methods, not Python-only
  ones such as `zfill`, `sort` or `copy`.
- Python and Starlark: record types, `{name: str, pid: int}`, in
  annotations and type comments, and alias comments `# type Name = T` to
  name them (Starlark has no alias or annotation syntax). A record type is
  exact: no missing or extra fields. A Python type alias may now name one
  declared after it, or itself.
- Python and Starlark: `r.get("key", default?)` on a record with a literal
  key gives the field's type (a key the record lacks is an error), when `r`
  is known to be a record at the call.
- Python and Starlark: a name in a type alias that names nothing (not an
  alias, not in scope, not bound by the program) is reported, instead of
  leaving what it types unchecked.
- Python: a name read only in a keyword argument's value
  (`f(xs = [o])`) was reported as undefined; scope resolution, and the
  language server's walks, now visit keyword arguments.

### Diagnostics

- A function that doesn't use `this` met by one that reads it, deep in two
  types compared as a whole (a class's instance against what its uses
  expect), names the member they are (`editor.say`) and shows both
  function types; the error was reported at the whole class with
  neither.
- A type mismatch inside two records (an object passed to a constructor
  or function whose parameter type is a large record) names the member
  that doesn't fit and shows that member's two types: ``Type mismatch in
  member `ask`: expected '(String) => String', found '(Number) =>
  Number'``, with the two whole records, trimmed to that member, in a note
  (and the note on record invariance when that is the cause). The error
  used to show the two whole records. A mismatch in a member's function
  parameters or array elements is that member's (`cb`, not `cb.x`).
- Type errors hold the types they compare and are rendered once, when
  reported, instead of when raised: a speculative attempt's error costs
  no rendering (and keeps no types where it can't be seen), so `subsume`
  can keep it, which is what lets it name the member.
- A mismatch between two types says where each side's part came from,
  as labels in the files they are in: for a function that reads `this`
  against one that doesn't, the call that made it a method (`o.ask(…)`,
  which passed its object as `this`) and the field of the object literal
  that is a plain function (or a method); for a member mismatch, the
  call or property read that gave the inferred side its type and the
  field of the object literal (passed directly, or by the `const` bound
  to it) that gave the other. A function's `this` bound to its object
  makes a recursive type: the type remembers the calls, so they are
  found after the class is generalised and used from another module.

### DOM declarations

- Nodes: `firstChild`, `lastChild`, `nextSibling`, `previousSibling`,
  `childNodes`, `nodeType`, `nodeValue`, `isConnected`; elements also
  `parentNode`, `offsetParent`, `getClientRects()` and
  `replaceChildren(...nodes)`.
- `document.createTextNode`, `createRange`, `getSelection`,
  `elementFromPoint`, `caretPositionFromPoint`, `caretRangeFromPoint`,
  `hidden`, `visibilityState` and `fonts.ready`.
- New types `DOMRect`, `Range<T>`, `Selection<T>` and
  `CSSStyleDeclaration`: an element's `style` and `getComputedStyle(el)`
  give the common properties as strings (`display`, `left`, `fontSize`,
  `cssText`, …) besides `getPropertyValue`/`setProperty`.

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

- Unifying recursive types always ends, with no depth limit: the "Type
  too complex: unifying these recursive types did not terminate" error is
  gone. Its cause was a row whose tail led back to itself (`ρ = {| ρ}`, met
  where two mutually recursive classes' rows meet), which inty made into
  the recursive type `μX. {| X}`: a row that never ends, which extended
  any row it was unified with forever. A row ending in itself is now no
  recursive type: with no fields the equation says nothing, and
  `ρ = {F | ρ}` gives `ρ` the fields `F` and a new tail. A recursive type
  met by a variable is compared once, keyed by the variable, whatever its
  type looks like by then; together with the pairs of bound variables
  already compared once, unification visits finitely many pairs of nodes
  (Huet's unification of rational trees).
- The language server answers hover, completion, and signature help in a
  file with a type error. A single error anywhere used to turn them off for
  the whole file, though inference had typed every other statement.
- The language server parses a file as the CLI does. It parsed without the
  source text, so a `return` at the end of a line returned the next line's
  value, and TS-style class field types were dropped.
- A type alias that doesn't parse is reported, and the rest of the file is
  still checked (the alias is an error type where it's used). It used to
  stop inference before the first statement, and the language server
  dropped the error, leaving a file with no diagnostics and no hover.
- `infer_program*` fails exactly when it collected an error, and the error
  it returns is the first collected. A read before initialisation used to
  be collected while the call succeeded.
- Hover on the name of an `export function`, `export async function`,
  class, or Lua `local function`. Their name's position was guessed from
  the statement's start, which lands in `export`, `class`, or `local`.
- An unknown type in a function type, `{ run: (String) => Item }`, is named
  (`unknown type 'Item'`) instead of reported as "expected ',' or ';'
  between object-type properties".
- `/** const a: …, b: … */` no longer splits a declarator at a comma inside a
  string literal type (`"a, b"`) or after an arrow inside type arguments
  (`Pair<() => A, B>`).
- An empty comment `/**/` ends at its own `*/`. It used to be read as the
  start of a doc comment running to the next `*/`, swallowing the code in
  between.
