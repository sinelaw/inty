# Patterns and idioms

Patterns for checking a real application with inty, collected from
[Rosaclef](https://github.com/sinelaw/rosaclef)'s `web/` (a ~6k-line
vanilla-JS DAW frontend, see [rosaclef-report.md](rosaclef-report.md)).
Some are good architecture whatever the checker; others worked around
inty's gaps. Each says whether it is still needed.

## Typed FFI boundary

*Still recommended.*

Keep untyped browser APIs behind one module whose typed surface is a
declaration file, and have the rest of the code import the module by a
mapped name:

```
web/
  lib/platform.js        plain JS, not checked: the browser API calls
  types/platform.d.js    its typed surface (declarations only)
  src/…                  import { listen, canvas2d } from "#platform"
```

```javascript
// types/platform.d.js
/** type Geo = { x: Number, y: Number, w: Number, h: Number } */
/** const measure: (Handle) => Geo */
export const measure;
```

The mapping lives where each tool looks for it:

- inty: `inty.json` `"paths": { "#platform": ["./types/platform.d.js"] }`;
- Node (tests): `package.json` `"imports": { "#platform": "./lib/platform.js" }`;
- the browser: an `<script type="importmap">` in `index.html`.

inty now also reads `package.json` `"imports"`, and prefers a `.d.js` next
to the `.js` it maps to. Putting the declarations beside the runtime file
(`lib/platform.d.js` next to `lib/platform.js`) makes `inty.json`
unnecessary. A mapped specifier always wins over a same-named file on
disk, as in Node.

The stdlib now covers much more of the platform (DOM events, canvas,
WebSocket, `ResizeObserver`, Web Audio, `fetch`, media devices, see the
[report](rosaclef-report.md)), so fewer APIs need the boundary; it remains
the way to type anything the stdlib doesn't, and to keep the checked code
testable without a browser.

**Buffer views** are one such API: `new Float32Array(memory.buffer, ptr,
len)` would make the constructor's first parameter `Int | ArrayBuffer`,
which an unannotated argument can't choose between, so the stdlib declares
only `new Float32Array(n)`. Declare the view in the FFI module:

```javascript
/** const f32view: (buffer: ArrayBuffer, byteOffset: Int, length: Int) => Float32Array */
export const f32view;
```

## Global alias lib

*Still recommended; the load-order constraint is gone.*

Shared type aliases live in one declaration file loaded with `--lib`
(`web/types/globals.d.js`). Aliases may now refer to aliases and classes
declared later in the same file, or recursively to themselves, so there is
no need to order them bottom-up or to put classes in a separate file loaded
first.

## Brand newtypes

*Use `nominal type` instead of empty classes.*

Integers with different meanings should not mix. Rather than an empty
`class InsertIx {}` per brand, declare nominal types next to the aliases
that use them, with identity casts in a small module (`x => x` at runtime):

```javascript
// globals.d.js
/** nominal type InsertIx = Int */
/** nominal type TrackIx = Int */

// brands.d.js (brands.js: `export const insertIx = (n) => n;` …)
/** const insertIx: (Int) => InsertIx */
export const insertIx;
/** const insertIndex: (InsertIx) => Int */
export const insertIndex;
```

`InsertIx`s compare with each other; `ix + 1` and `xs[ix]` need
`insertIndex(ix)`; an `InsertIx` is rejected where a `TrackIx` is
expected. See [design-notes.md](design-notes.md#newtypes--use-nominal-type).

## Dictionaries

*Entry-list codecs are no longer needed.*

A JSON object used as a map is a `Dict<V>` (also `{ [String]: V }`):

```javascript
/** type Device = { type: String, enabled: Boolean, params: Dict<Number> } */
const cutoff = device.params.cutoff ?? 1000;      // a read may miss: V | Undefined
for (const [key, value] of Object.entries(device.params)) { … }
```

Decoding `{key, value}[]` lists (and encoding them back) was only needed
because there was no such type.

## Dynamic output objects and generic decoders

*Still useful; `Dict<V>` covers the homogeneous case.*

`JSON.parse` returns a fresh type variable, so a generic decoder lets each
call site say what shape it expects:

```javascript
/** function decode<T>(text: String) => T */
function decode(text) { return JSON.parse(text); }
/** const project: Project */
const project = decode(text);
```

Build an outgoing message with an object literal of the right shape, or a
`Dict<V>` when its values have one type, rather than an open object from
`JSON.parse("{}")`.

## Flat description buffers and integer handles

*Still good design; no longer needed for speed or to avoid recursive aliases.*

Rosaclef's UI builds a flat array of nodes with parent indices and talks to
a backend through `Int` handles (a DOM backend in the browser, a memory
backend in Node tests). That keeps the UI testable without a browser.
Recursive aliases (`type Node = { children: Node[] }`) now work, and inty no
longer slows down on the DOM's big rows (the cost was copying them, see
[performance.md](performance.md)), so neither the flat buffer nor the
handles are needed to make the checker cope.

## Records instead of tuples

*No longer needed.*

Tuples are types: `[String, Number]`. An array literal where one is
expected is one; `t[0]` reads the first element with its own type, and
`const [a, b] = t` destructures. An unannotated heterogeneous array literal
is an error that suggests a tuple, a record, or an element union.

## Loops instead of `find` and narrowing on module-level data

*No longer needed.*

`XS.find(…)` on a module-level array, then `found ? found.v : ""` (or `!==
undefined`, `!= null`, `&&`, an early return), now narrows: a function
declaration is checked after the module-level declarations it reads, so it
sees their types.

A mutable binding (`let`) isn't narrowed, because anything that runs in
between may write it. Copy it to a `const` first:

```javascript
const t = term;
if (t !== undefined) t.write(s);
```

## Explicit numeric annotations

*Mostly no longer needed.*

A field initialised with an integer literal takes its type from its uses
(`{ volume: 1 }` then `state.volume = 0.5` makes it a `Number`), across
modules too: an imported module's integer-literal fields are decided by
its importers' uses. An annotation is still needed where both happen — a
field used as an index (an `Int`) *and* given fractions — and the error then
says so, with the annotation to write:

```
Error: Type mismatch: expected 'Int', found '0.5'
  Help: 'volume' was inferred Int from its integer initializer and its
  uses; if it holds fractions, declare it a Number where the object is
  written: `volume /*: Number */: 0`
```

A non-literal `Int` (`xs.length`, `Math.round(x)`) now fits a `Number`
field of a returned or annotated record, and a callback's result.

## Typed empty-array seeding for late-initialised state

*No longer needed.*

Late-initialised module state is a `let` of a union:

```javascript
/** let term: Term | Undefined */
let term = undefined;
function attach(t) { term = t; }
function say(s) { const t = term; if (t !== undefined) t.write(s); }
```

## Rank-1 workaround: top-level generic functions

*Still needed.*

A function stored in a record has one type for all its uses; keep generic
helpers at the top level and call them by name. See
[design-notes.md](design-notes.md#polymorphic-record-fields--rank-1-only-with-a-clearer-error).

## Enriched event rows

*Mostly no longer needed.*

Event listeners get a `DomEvent<T>`: one shape with the fields of pointer,
mouse, wheel, keyboard, input, focus, touch, drag and clipboard events
(`clientX`, `button`, `buttons`, `shiftKey`, `key`, `code`, `deltaY`,
`dataTransfer`, `target`, `preventDefault`, …). Read only the fields the
event you listen for has; a field of another kind reads as `undefined` at
runtime. Converting native events into a flat record of your own is still
the way to add computed fields (`targetLeft`) or to keep handlers testable
with a memory backend.

## `.catch((e) => Promise.resolve(false))`

*No longer needed.* A `then` or `catch` callback may return a value or a
promise: `.catch((e) => false)`.

## Handlers ending with `return undefined;`

*No longer needed.* A function falling off its end returns `undefined`,
and a concise arrow passed where the result is `Undefined` runs for its
effect: `(e) => list.push(e)`.

## Index-taking callbacks and zero-parameter callbacks

*No longer needed.* `xs.map((x, i) => …)`, `filter`, `forEach`, `some`,
`every`, `find`, `findIndex` and `reduce` pass the index (and the array),
and a callback may take fewer parameters than it is passed
(`xs.map(() => 0)`).

## Per-module checking

*No longer needed.* Errors in an imported module are reported in that
module (with a "required here" label where a generic function's body
requires what failed), each module is checked once per run, and
`inty src/*.js src/ui/*.js test/*.js` checks the whole tree in one run
(Rosaclef: 1.5 s). `inty --timings` shows where the time goes.

## AudioWorklet processors

*Now checkable.* An AudioWorklet module can be checked with
`--lib builtin:audioworklet`, which declares `AudioWorkletProcessor`,
`registerProcessor`, `sampleRate`, `currentTime` and `currentFrame`;
`class P extends AudioWorkletProcessor { … }` is supported. A class
constructor may only assign fields (`this.x = …`) after `super(…)`; keep
any other set-up in methods.
