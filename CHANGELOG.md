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

- An array met by a record of reads (`o.xs.map(f)` while `o` isn't known,
  later given an array) has every field the record needs, of the type a
  read of it has: only `length` was known, so any method read failed
  ("Property 'map' not found on type …[]").
- A member's flags not agreeing (assigned against read-only, own against
  on the prototype) is a mismatch in that member: the error named neither
  member nor types.
- Writing out a type for a diagnostic stays within its budget: a part
  written before (memoised) or stored in place was written whole, which
  for a type sharing its parts (elements chained through `appendChild`)
  ran out of memory.
- A failure inside a member of two records (or a class instance and a
  record) that isn't a plain mismatch (a property an array lacks, an
  arity, an infinite type) names the innermost member it is in and shows
  that member's two types, with the failure as the reason: ``Type mismatch
  in member `view.pane.rows`: expected '{size: Number}', found
  'Number[]'`` (help: `Property 'size' not found on type Number[]`). It
  used to show the two whole types only. Unrolling a recursive or nominal
  type keeps the two sides' order, so such a member's expected and found
  aren't swapped.
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

### Browser APIs

- Typed arrays: `Int8Array`, `Uint8ClampedArray`, `Int16Array`,
  `Uint16Array` and `Uint32Array` join `Int32Array`, `Uint8Array`,
  `Float32Array` and `Float64Array` (each with `BYTES_PER_ELEMENT`; the Go
  backend stores into them as JavaScript does, a `Uint8ClampedArray`
  clamping). `new T(…)` is typed by its first argument's type: a length
  (or nothing), a view of an `ArrayBuffer`, `new Uint32Array(buffer,
  byteOffset?, length?)`, or a copy of a `Number[]` or another typed
  array. A buffer view no longer needs a declaration of its own.
- `TextEncoder.encode` gives a `Uint8Array`, and `encodeInto(string,
  bytes)` gives `{read, written}`; `TextDecoder(label?, options?)`'s
  `decode` takes a `Uint8Array` and `{stream}`.
- WebAssembly: a compiled module is its own type, `WebAssemblyModule`,
  and an instance `WebAssemblyInstance<E>` (`{exports: E}`).
  `WebAssembly.instantiate(bytes, imports?)` resolves to `{instance,
  module}`, `instantiate(module, imports?)` to the instance; `compile`,
  `new WebAssembly.Module(bytes)` and `new WebAssembly.Instance(module,
  imports?)`. What reads bytes takes a `BufferSource` (an `ArrayBuffer`
  or any typed array).
- `Error` is a type name (`(Error) => Undefined`); the error
  constructors take an optional message.
- `Worker<I, O>` (`new Worker(url, {type: "module"})`) and
  `MessageChannel<M>`; a worker's own scope, `self` (a
  `WorkerScope<I, O>`) and `postMessage`, with `--lib builtin:worker`.

### Generators

- `function*` declarations, expressions and `export`s, and `*m() { … }`
  methods of classes and object literals; `yield e`, `yield* it`, a bare
  `yield`, and `return` in them. A generator gives an `Iterator<T>` of
  what it yields (`{next: () => {done: Boolean, value: T},
  [Symbol.iterator]: T}`, in the stdlib), which `for … of`, a spread and
  `Array.from` iterate; an annotation `=> Iterator<T>` checks each
  `yield` against `T`. The printed program writes them as written.
  `async function*` isn't taken.

### DOM declarations

- `el.focus({preventScroll, focusVisible})`; an event's `detail` (a
  click's count); `append`, `prepend`, `before`, `after` and
  `replaceChildren` take several nodes (up to eight; inty has no variadic
  function type). Strings, which JavaScript also takes, aren't declared
  yet: a `T | String` parameter doesn't take an element whose node type a
  call hasn't pinned down.
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

- `Object.freeze({fg, wavy: null})` returned where a `{fg: String | Null,
  wavy: String | Null}` is expected was rejected (`wavy`'s `Null` isn't
  `String | Null`), though the literal itself was accepted there: a call
  of a function giving back its argument, `<a>(a) => a` (`Object.freeze`,
  `structuredClone`, a program's own identity), where a type is expected
  now checks its argument against that type.
- A class whose method reads `this` (`get(i) { return this.n + i; }`)
  took a type parameter (`class 'A' takes 1 type argument (a type in
  method 'get')`), so `/** function f(a: A) */` was rejected: the
  method's `this` is the instance, a cycle the class's type is written
  out through, and the variable where that cut it was taken for one the
  class leaves open.
- A module's reads of a field of a value an importing module gives
  (`y.k` in a method an importer calls) wait for the importer's value,
  each resolved against its type. The first read of each name became the
  field of a record and the others were dropped: what they asked of the
  value was lost (with `const r = y.k; y.k.toUpperCase();`, an importer's
  `{k: 1}` was accepted, and rejected with the two reads the other way
  round), and an array or a string given didn't fit the record (an
  array's `map` read twice, at two types). So do the module's other
  requirements on such a value (an `Iterable`, an index, a store, a
  test), which were dropped at its end, and a module imported in between
  (one that imports none of what reaches the value) no longer decides
  them first. A read decided at a module's end leaves the field's kind
  open, as a read does: a getter or a class's method given for it fits.
  Fresh's web client: 22 errors to 11.
- A method call a generic function makes on its parameter (`ed.say(…)`)
  checks the method's own `this` against the receiver when the argument
  is known, as a direct call does: a method of another object, read off
  it (`new K().say`), was accepted, and ran with the wrong `this`.
- Generalising no longer depends on the order the checker meets things
  in: what a type reaches through a cycle of bindings is the same
  wherever a walk enters it, and a recursive type's body found to have no
  free variable during a speculative attempt is looked at again once the
  attempt is undone (a variable it held could be generalised). A
  type annotation's variables escaping into the context are found through
  any binding, not only the one of a variable's own.
- Binding a variable no longer walks everything the type it is bound to
  reaches (the occurs check, and the check for a recursive type) when the
  type can't reach the variable, which is what an index of the bindings
  mentioning each variable says: binding a variable to a type holding a
  large object went through the whole object each time. Fresh's web
  client: 12 s to 10 s, its `App` about 2.7 s to 1.7 s.
- Checking is faster where many functions are generalised with inferred
  recursive types around (an object whose methods take it as `this`), and
  inside large functions: Fresh's web client took 340 s, now 14 s (its
  `App` 30 s to 3 s, `Pane` 13 s to under 1 s). To find what the
  environment fixes, generalising walked through the substitution from
  each of the environment's variables, each such type's body, and each
  waiting constraint's types, on walks of their own, at every
  generalisation (nested functions' too). They are now one walk, and what
  it reaches is kept from one generalisation to the next, brought up to
  date from the bindings made since. A record's fields are shared between
  copies of it until one is changed: an object with many methods was
  copied whole at each binding read and each unification. And binding a
  variable to a row no longer copies the row's fields first to check
  whether it ends in that variable, which it rarely does.
- The fields a spread gives an object literal are fitted to the expected
  record before the members written after it are checked: in
  `list({ ...listProps(items), onActivate: (it) => … })` the spread's
  `items` says what `it` is, as `items` written out does, so `it.kind ===
  "ws"` narrows a union of records rather than fixing an unknown `kind`
  to `"ws"` ("expected '"header"', found '"ws"'").
- A method call on a value an importing module decides
  (`editor.say("hi")` on a `let editor` an importer sets) takes a
  function that uses no `this` as well as a method of the receiver, as
  JavaScript does (an arrow function ignores the receiver). The callee
  became a method of the receiver as the module ended, so an importer's
  `{ say: (t) => … }` was "a function that doesn't use `this`" where
  "one that reads `this`" was expected. Its `this` now waits for the
  importers and is still settled as a method of the receiver when
  nothing else decides it (also when a function the importer generalises
  first reaches it).
- A value of a type not known yet that is both iterated and read from
  (`for (const o of xs) …` and `xs.find(…)`) is a record of what its uses
  read, `[Symbol.iterator]` among them: an array fits it. Iterating such a
  record was an error ("an object isn't iterable"). A closed record, or one
  known to lack an iterator, still isn't iterable.
- A field written after a spread in an object literal is checked against
  the expected record's field, as it is without the spread: a callback
  given to `{ ...ui.BUTTON, onClick: () => { … } }` may take fewer
  parameters than its slot passes. It was inferred on its own and then
  compared, so `(s) => …` didn't fit `(String, Number) => Undefined`.
- A function value taking fewer parameters than its slot passes fits it
  (`ui.listProps("cards", ws, card)` with `const card = (w) => …`), as a
  function literal written in the call does: JavaScript drops the extra
  arguments. Only a literal was accepted; a named function, or one bound
  to a `const`, was "expected '(T, Number) => R', found '(T) => R'". Its
  parameters must still take what the slot passes and its result be the
  slot's; one needing more arguments than the slot passes is still
  rejected.
- Two recursive aliases being compared are assumed equal, while compared,
  as the instances they are, arguments included. Keyed by their ids alone,
  `P<Number>` agreeing with `Q<Number>` let `P<String>` agree with
  `Q<Number>` too: with `type P<A> = {v: A, next: P<String>}` and `type
  Q<A> = {v: A, next: Q<Number>}`, a `Q<Number>` passed as a `P<Number>`
  was accepted, and its `next.v`, a number, read as a string.
- A recursive alias whose recursive use builds a larger argument from its
  own parameter (`type Nest<A> = {next: Nest<{w: A}>}`, directly or
  through an alias it is defined with) is rejected where it is declared:
  its unrollings are ever larger types, so comparing two of them, keyed by
  their arguments, needn't end. A recursive use may pass the alias's own
  parameters, in any order, or types that don't mention them
  (non-expansive definitions, Kennedy and Pierce 2007).
- Unifying recursive types always ends, with no depth limit: the "Type
  too complex: unifying these recursive types did not terminate" error is
  gone. Its cause was a row whose tail led back to itself (`ρ = {| ρ}`, met
  where two mutually recursive classes' rows meet), which inty made into
  the recursive type `μX. {| X}`: a row that never ends, which extended
  any row it was unified with forever. A row ending in itself is now no
  recursive type: with no fields the equation says nothing, and
  `ρ = {F | ρ}` gives `ρ` the fields `F` and a new tail. Two rows whose
  tails lead, through the rows they are bound to, to the same tail (spreads
  whose result flows back into their operand: `o = {...{...o, a: 1}, b: 1}`)
  are compared as the one row each is, the shared tail taking the fields
  only one lists; taken a row at a time, each extended the other's bound
  tail with a fresh one without end. A recursive type met by a variable is
  compared once, keyed by the variable, whatever its type looks like by
  then.
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
- An annotation that doesn't parse (`/** function f(a: String) => Item */`
  with `Item` undeclared) is reported, and the function or variable it
  annotates is checked as if it had none. The whole declaration used to
  fail, so its body was never checked: its parameters and locals had no
  types, and it was an error type wherever it was used.
- Hover off any name (in a function's body, or a declaration's initialiser)
  shows nothing. It used to show the enclosing function or variable.
- The language server resolves a saved file's imports, relative to it, as
  the CLI does: an imported name has its type, where it used to be an
  undefined variable. Only the open file's own errors are shown. Both build
  a program's environment (prelude, imports, Starlark `load`s) with
  `frontends::program_env`; the language server now starts Python and Lua
  from the same stdlib as the CLI, and Python from stdin sees its prelude.
- Hover and hints print types as diagnostics do, with one printer
  (`InferState::printer`): a type that is an alias's body, its parameters
  instantiated, by the alias's name (`items: PaletteItem[]`, `Box<Number>`),
  where they printed the whole record. A function type matches an alias's
  when it prints as the alias's: a checked annotation gives an unstated
  `this` none, which kept a record with a method from matching its alias,
  in diagnostics too.
- Hints leave out what an annotation states: the parameters and return
  type of a function with a `/** function f(x: T) => R */` annotation, and
  a variable annotated `/** const x: T */`. They repeated it, at length.
- `inty.json` is found from the file checked however it is named: `inty
  js/a.js` looked from `js` up to the working directory only, so a config
  above it (its `"libs"`, `"paths"`) was missed.
- `inty.json` `"libs"`: declaration files every module under the config
  is checked with, as `--lib` loads them, found from the file checked (the
  nearest `inty.json` above it). The language server, which takes no
  `--lib`, checked a project whose types live in a shared `.d.js` without
  them: every annotation naming one of its types failed, and was ignored.
  An entry's project libs are loaded once per run, a lib's errors are
  reported against it, and a config or lib that doesn't read against the
  entry.
- An import that fails (a path that doesn't resolve, a cycle, a name the
  module doesn't export) is reported, and its names are `Error`; the
  importer is still checked. It used to stop the importer.
- A module with type errors is reported against itself, and its importers
  see what it typed. It used to fail whole, every name imported from it
  `Error`.
- Hover on a member's property (`s.startsWith`, `o.a.b`) shows its type.
  It showed nothing: hover knew only names, and a method call's callee
  (`obj.m`) wasn't among the expression types inference records.
- Hints and hover name type variables one way, decided once per
  document: per top-level declaration, in reading order (`matching(items:
  a, q: b) -> c`). Hints were named across whatever range the editor asked
  for, so the same binding read `hits: b1` in one view and `hits: c` in
  another, and hover named its own (`hits: a`). Hover shows a binding as
  its hint does, with the constraints its type reaches (`hits: c where c
  has {map: …}`), and a generic binding's own variables (`<a>(a) => a`);
  a variable's `has` constraints print as one (`o has {label: u, detail:
  v}`).
- Hover shows what inference recorded for the word under the cursor: a
  name's declared type, or else the type of the innermost expression the
  word begins or ends (or the literal it is in) — `this`, a literal, a
  global, `new Map()`, each link of `o?.a.b`. It computed types of its own
  for a few cases and showed nothing for the rest. A test now walks every
  expression of the example programs and requires a recorded type for
  each, so a path that types an expression without recording it fails it:
  `check_expr` records in one place, as `infer_expr` does, and an optional
  chain records each link.
- A type error inside a function's body, a block, or a class's method no
  longer stops the rest of it being checked: a statement list collects what
  fails and goes on, at every depth, not only a program's top level. One
  error early in a class used to leave every method after it unchecked
  (no types, no hover).
- A generalised function's scheme no longer carries constraints on
  variables its type doesn't reach. A local generic `const` that read a
  variable of the enclosing function (`const lead = (it) =>
  it.label.startsWith(t[0])`) left a copy of its own constraints in the
  enclosing function's scheme (`y1 has {label: v1}, v1 has {toLowerCase:
  …}, …`), over variables no caller sees; so did a discarded function's
  parameter. Of the constraints a scheme takes, it now keeps only those
  whose subject (a receiver, a container) its type reaches: in every
  instance the others are on a fresh variable that can be whatever meets
  them. What stays pending is unchanged.
- Iterating a value an enclosing function returns, decided later as one
  that isn't iterable, is an error:
  `if (c) { const t = JSON.parse(s); for (const x of t) {} return t; }`
  then a generic local `const` and `return id(0)`. Generalising the local
  `const` deleted the pending `Iterable`, judging it unused, though the
  `return` would decide its container.
- `/** const a: …, b: … */` no longer splits a declarator at a comma inside a
  string literal type (`"a, b"`) or after an arrow inside type arguments
  (`Pair<() => A, B>`).
- An empty comment `/**/` ends at its own `*/`. It used to be read as the
  start of a doc comment running to the next `*/`, swallowing the code in
  between.
