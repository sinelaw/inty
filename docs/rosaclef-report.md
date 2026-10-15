# Rosaclef as a regression corpus

[Rosaclef](https://github.com/sinelaw/rosaclef) (branch
`claude/affectionate-pascal-cxcj39`, checked at `4f88bd5`) is a DAW
frontend of about 4.8k lines of vanilla ES modules under `web/` (19
checked files, 21 modules with their declaration files), built on inty.
Its `docs/inty-notes.md` logs the bugs, confusing diagnostics, slow checks
and missing library declarations that building it turned up. This page is
the status of each of those items, the final run over `web/`, and which of
Rosaclef's workarounds can now go.

Related pages: [performance.md](performance.md) (item 18),
[design-notes.md](design-notes.md) (items 22–24),
[patterns.md](patterns.md) (the idioms Rosaclef invented).

There have been two rounds. The second, [below](#second-round-moving-to-inty-cb4bfca),
covers the gaps Rosaclef found moving from inty `0439e15` to `cb4bfca`
(its notes' section "Gaps found moving to inty `cb4bfca`", items A–G).
The first, from [Final run](#final-run) on, covers the items numbered
1–24.

## Second round: moving to inty `cb4bfca`

Rosaclef branch `claude/gallant-planck-ermxo9` at `913758b`: 64 files
under `web/`, checked by `web/check.sh` in one run.

```
$ cd web && sh check.sh
…
1 of 64 files had errors
```

| | `cb4bfca` (main) | this branch |
|---|---:|---:|
| `web/check.sh` | killed at 15 GB after 4.5 min | 5.8 s (8 s without mimalloc) |
| tree/tree.js on its own | 155 s | 0.1 s |
| tree/memory.js on its own | 3 s | 0.03 s |

- **The one remaining error is Rosaclef's**, and by design:
  `errText(e)` in `src/ui/mixcheck.js` reads `e.message` of a caught
  exception. Anything can be thrown, so since `faa297b` a caught value has
  an opaque type: it can be passed on, tested and rethrown, but not read
  as a record ([type-system.md](type-system.md)). `0439e15` accepted it.
  The message now says so and suggests `String(e)`.
- Before this round an error in an imported module was printed once per
  importer (12 times here), and every importer of the failing module was
  checked again and failed with it, its own code unchecked. A module that
  fails is now reported once and checked once; its importers go on, with
  what it would have bound typed `Error` (test
  `a_failed_module_is_checked_once_and_its_importers_still_are` in
  `modules.rs`).

| Item | Status | Tests |
|---|---|---|
| A. Checking 100× slower, out of memory | Fixed | `tests/checking_time.rs` |
| B. A record field can't hold a callback | Fixed | `gap_b_a_record_field_holds_a_callback`, `a_record_field_holds_a_callback`, `a_method_and_a_detached_function_are_different_types`, `a_literal_method_fits_the_slot_it_is_checked_against` |
| C. The `this` mismatch doesn't say `this` | Fixed | `gap_c_a_detached_method_call_says_this` |
| D. `(x ?? {}).f` | Not changed (reasons below) | `gap_d_a_field_of_an_empty_default`, `a_field_of_an_empty_default_is_not_read` |
| E. `arr.length = 0` | Fixed | `gap_e_array_length_store`, `a_store_to_an_array_length_truncates_it` (checking and evaluation) |
| F. `c ? x : undefined` | Fixed | `gap_f_conditional_with_nothing`, `a_branch_of_nothing_makes_the_conditional_a_sum` |
| G. `Array.prototype.at` | Fixed | `gap_g_array_at`, `an_array_at_may_be_undefined` |

The `gap_…` tests are in `crates/inty/tests/rosaclef_regressions.rs`
(each is the repro from Rosaclef's notes); the others are in
`crates/inty/src/infer/tests.rs` and `crates/inty/src/dynamics/tests.rs`.

**A. Checking time.** Since `74c2460` a function type in an object type
was a method whose `this` is the object, so every record type with a
function field was recursive, and each use of it made fresh rows that were
unified against each other. Now a function type, `() => T`, is a function
that uses no `this` (it is never bound to a receiver), and a method is
written as a method signature, `m(): T` (see B). Records with callbacks
are not recursive any more. The rest came from copying types: resolving a
type copied it whole at every step of a unification and of each check, and
a module that failed was checked again for each importer. Unification and
the common checks now resolve only the part of a type they look at, and a
failed module is checked once. The CLI also uses the mimalloc allocator;
the system allocator spent about half of the time. Details in
[performance.md](performance.md#second-round-annotated-function-types).
`tests/checking_time.rs` checks a program shaped like Rosaclef's (a
record with 25 methods, 60 functions using it) and fails over 10 s; it
takes about 1 s.

**B. Callbacks in records.** In an object type, `stop: () => Undefined`
is a function that uses no `this`, which can be stored, read back, called
detached and passed on. `stop(): Undefined` is a method, called on the
object. A function that reads `this` can't be stored in the first: it
would be called detached. An arrow, or a function that never mentions
`this` (an object literal's method included), fits either. So the
wrappers Rosaclef added
(`fn: (e) => fn(e)`, `paint: (g, w, h) => d.paint(g, w, h)`) can go.

**C. Diagnostics.** A detached call of a method (`const end = s.stop;
end();`) says "`end` is a method (it reads `this`), so calling it detached
passes `this` = undefined", and suggests calling it on its object or
giving it no `this`. A
function that reads `this` where one that uses none is expected says
that, and suggests a method signature. A method in a record type prints
as `stop(): Undefined`, not `this: {…} => () => Undefined`.

**D. `(x ?? {}).f`: not changed.** `{}` is a record with no fields, so
`(raw.c ?? {}).off` reads a field one side doesn't have. There are two
ways to accept it, and both are worse:
- an open `{}` (a record with unknown other fields) would make a later
  read of any field succeed, on a value that doesn't have it;
- an optional field read as `T | Undefined` (TypeScript's `off?: T`)
  needs absent fields in record types, which inty doesn't have: its
  `off?: T` is a field that may or may not be in the type, and reading it
  requires it.

Rosaclef's rewrite is the way to write it: tell the absent case apart
first, `if (!c) return …; … c.off ?? []` (its `decodeCritic`).

**E. `arr.length = 0`.** An array's `length` takes a number (only an
array's: a string's and other built-in properties still can't be
assigned). A store truncates the array. A store of a larger length, which
would leave holes, is an index fault, like reading past the end.

**F. `c ? x : undefined`.** When one branch is exactly `undefined`
(or `null`), the conditional is the other branch's type or `Undefined`
(`Null`): `xs.length > 0 ? xs[xs.length - 1] : undefined` is
`Number | Undefined`. Other branches of different types are still an
error unless an annotation says what the result is.

**G. `Array.prototype.at`.** `xs.at(i): T | Undefined`, since an index
past either end gives `undefined`.

## Final run

```
$ cd web
$ inty --lib types/newtypes.d.js --lib types/globals.d.js src/*.js src/ui/*.js test/*.js
All checks passed: 19 files (21 modules checked, 16 as imports) in 1.46s
```

- **Remaining errors: none.** Every module Rosaclef's `check.sh` covers
  checks, in one run, unmodified.
- **Total check time: 1.5–1.6 s** in one process (1.7–1.9 s wall clock,
  including loading the built-in declarations). Before this round the
  unmodified inty stopped at the first `new Date()` within 3 s; with only
  the bug fixes, `main.js` alone ran for more than 25 minutes before it
  was stopped (see [performance.md](performance.md) for each module).
- `engine/worklet.js`, the AudioWorklet processor, was never checked
  (no `extends`). It now parses up to its constructor, which does more
  than assign fields (`this.port.onmessage = …`); see
  [What still needs a workaround](#what-still-needs-a-workaround).

## Workarounds that can be deleted

Measured on a copy of `web/` with the workarounds removed (the patch is
31 insertions, 214 deletions over 19 files); the whole tree still checks in
one run in 1.56 s, and `node test/tree.test.js` still passes.

| Workaround | Count removed | Why it can go |
|---|---:|---|
| `return undefined;` ending handlers and callbacks | 188 | falling off the end returns `undefined` (item 12) |
| `.catch((e) => Promise.resolve(false))` | 9 | `then`/`catch` callbacks may return a value (item 9) |
| `/*: Number */` on integer-initialised state fields | 15 | fields take their type from their uses (item 5) |
| `types/newtypes.d.js`, loaded first | 1 file | classes and aliases resolve in any order (item 4); the brands become `nominal type`s in `globals.d.js` (item 23) |
| `check.sh`'s one process per module | — | one run checks every file, each module once, errors in the right file (items 13, 18) |

These can also go, but each takes a small rewrite rather than a deletion,
so they weren't part of the measured patch:

- `{key, value}[]` entry-list codecs for JSON maps in `src/model.js` →
  `Dict<Number>` (item 22).
- `{l, r}` / `{key, value}` records used as pairs → tuples (item 10).
- `for … of` loops with early returns in place of `.find()` plus
  narrowing → `.find()` (item 2).
- Typed one-element arrays for late-initialised state
  (`const term: Term[]`, `term.push(t)`) →
  `/** let term: Term | Undefined */` read through a `const` copy.
- `promptBox` in the platform layer, used instead of `window.prompt` →
  `window.prompt(message, default)` (item 15).
- The enriched event rows built by the platform layer, where handlers
  only read native fields → `addEventListener` callbacks get a
  `DomEvent<T>` (item 19).
- The separate `newtypes.d.js` load order in `inty.json`/`check.sh`, and
  `inty.json` itself if `platform.d.js` moves next to `platform.js` (the
  `package.json` `"imports"` mapping is then enough, item 11).

[patterns.md](patterns.md) says, idiom by idiom, which are still worth
keeping as design (the typed FFI boundary, integer-handle backends,
top-level generic functions) and which were only there for inty.

## What still needs a workaround

- **Constructors that do more than assign fields.** A class constructor
  may assign `this.x = …` after `super(…)`; statements such as
  `this.port.onmessage = …` or loops have to move into a method called
  after construction. `worklet.js` also sets fields to `null` before
  they are ready; with a declared `T | Null` field type that works.
- **Typed-array views over a buffer.**
  `new Float32Array(memory.buffer, ptr, len)` isn't declared (an
  unannotated argument can't choose between the `Int` and `ArrayBuffer`
  constructors); declare a `f32view` in the FFI module (see
  [patterns.md](patterns.md#typed-ffi-boundary)).
- **Generic functions in records** stay rank-1: keep them top level
  (item 24).
- **Narrowing a mutable `let`** doesn't happen; copy it to a `const`
  first.
- **Per-name event types** (`"keydown"` giving a `KeyboardEvent`) need
  polymorphic fields; listeners get one `DomEvent<T>` shape (item 19).

## Items

Tests are in `crates/inty/tests/rosaclef_regressions.rs` (one per bug,
from the repro in the report, named `bN_…`), the golden diagnostics in
`crates/inty-cli/tests/golden/NN-…/` (run by `diagnostics_golden.rs`),
and module tests in `crates/inty/src/modules.rs` and
`crates/inty-cli/tests/import_diagnostics.rs`.

### A. Bugs

Before any of these, `new Date()` with no argument was rejected, which
stopped every Rosaclef module that reads the clock
(`new_date_without_argument`).

1. **Comparing operands read from module-level bindings.** The cause was
   the order of inference, not the comparison rule: hoisted function
   declarations were all inferred before the module's `const`
   declarations, so inside a function `state.insert` was an unsolved
   `HasProp` read on a variable, and the comparison unified two
   variables. Functions are now inferred lazily, in dependency order
   (strongly connected groups), after the declarations they read, and see
   their types. `>=`, `<`, `===` and `!==` accept any mix of `Int` and
   `Number`. Tests `b1_compare_outer_property_reads`,
   `b1_function_before_declaration`.
2. **Narrowing reads of outer bindings.** Same root cause as 1: once the
   outer type is known, `found ? found.v : ""`, `!== undefined`,
   `!= null`, `&&`, early returns and ternaries narrow. Tests
   `b2_narrowing_outer_find`, `b2_narrowing_forms_on_outer_bindings`.
3. **Forward references between aliases.** Aliases in a module or lib
   are collected first and resolved in dependency order; recursive and
   mutually recursive aliases are supported (`type Node = { children:
   Node[] }`), and an alias that is only itself (`type A = A`) is an
   error that says so. Tests `b3_alias_forward_reference`,
   `b3_recursive_aliases`.
4. **Lib classes invisible to aliases.** Class names are reserved before
   aliases are resolved. Test `b4_lib_class_visible_to_aliases`.
5. **Non-literal `Int` into `Number` positions.** A function literal
   checked against an expected type (an annotation, a callback
   parameter, a record field of an annotated return) is now checked
   against it, rather than inferred and then unified, so an `Int` result
   fits a `Number` field or result. A field initialised with an integer
   literal is decided by its uses, across modules; where both an `Int`
   and a fraction are required, the error names the field and the
   annotation to write (golden `05-int-field-given-a-fraction`). Tests
   `b5_int_into_number_positions`, `b5_literal_initialised_field`.
6. **Zero-parameter callbacks.** A function literal may take fewer
   parameters than the function type it is checked against. Test
   `b6_fewer_callback_parameters`.
7. **Index-taking callbacks.** `map`, `filter`, `forEach`, `some`,
   `every`, `find`, `findIndex`, `reduce` pass `(x, i, xs)`. Test
   `b7_index_callbacks`.
8. **`&&` / `||` / `??`.** When both operand types are known, the result
   is what can come out: `a && b` is `b`'s type joined with `a`'s falsy
   part, so `cond && maybeObj ? x : y` checks; the right operand is
   narrowed by the left. Test `b8_logical_operators`.
9. **`then`/`catch` callbacks returning values.** A callback may return
   `T` or `Promise<T>`. Test `b9_promise_callbacks_return_values`.
10. **Heterogeneous array literals.** Tuple types `[String, Number]`:
    an array literal where a tuple is expected is one, `t[0]` has the
    element's own type, and destructuring works. An unannotated
    heterogeneous literal is an error that suggests a tuple, a record or
    an element union (golden `10-heterogeneous-array`). Test
    `b10_tuples`.
11. **Mapped specifiers vs files on disk.** A mapped specifier wins over a
    same-named file, as in Node, and `package.json` `"imports"` (exact and
    `*` patterns, conditional targets) is read too; a `.d.js` next to the
    mapped `.js` is preferred. Tests in `modules.rs`
    (`package_json_imports_resolve_to_the_declaration_file` and the
    mapped-path test before it).
12. **`return undefined;` in handlers.** A function falling off its end
    returns `undefined`, and a concise arrow checked against an
    `Undefined` result runs for its effect: `(e) => hint("x")`. Test
    `b12_undefined_callbacks`.

### B. Diagnostics

13. **Errors in imported modules.** Every module's source is registered in
    a source map (each module's spans live in their own range), so a
    diagnostic is rendered in the file it is about. A module's pending
    constraints are solved when that module is done, so its errors are
    reported there. When a generic function's body requires what fails
    at a call in another module, the error carries both: "required here"
    in the callee's file and the call in the importer's. The misleading
    "from parameter 'pan'" labels came from a search of the whole
    substitution for any variable bound to an equal type; it is gone.
    Goldens `13-error-in-imported-module`,
    `13-required-by-generic-function`.
14. **Unbound type variables.** `function f(o: T) => Number` reports
    "unknown type 'T'" and suggests `function f<T>(o: T) => …`. Golden
    `14-unbound-type-variable`.
15. **"Presence mismatch".** A missing or surplus argument is now an
    arity error ("the function takes 1 argument, but 2 are passed"), and
    a field present on one side only names the field and shows both
    (trimmed) record types. The Rosaclef cause was two stdlib
    declarations that took one parameter: `window.prompt` (called with a
    default) and `console.log` (called with two values); both are fixed.
    The module-graph dependence was bug 13: an imported module's error was
    rendered at its byte offset in the importer's text, and a run stopped
    at the first error, so which call it landed on depended on the entry
    module. Goldens `15-arity`, `15-missing-field`.
16. **Huge rows.** A mismatched row prints the fields that differ plus
    "… and N more"; a type that matches a declared alias (generic ones
    too) prints as the alias's name. Goldens `16-big-row-trimmed`,
    `16-alias-by-name`.
17. **Type variable names.** Variables are renamed `a`, `b`, … per
    message, and a numeric-literal variable prints as `Number | Int`.
    Golden `17-type-variable-names`.

### C. Performance

18. See [performance.md](performance.md): the profile, the five fixes
    (speculation without copying the state, a persistent environment,
    solving imported modules' constraints, checking each module once per
    run, not formatting errors of failed speculation), before/after for
    each module, `--timings`, checking several files in one run, and
    source snapshots. The on-disk cache wasn't built: the whole corpus
    checks in 1.5 s.

### D. Standard library

19. **DOM events.** Listeners get a `DomEvent<T>` with the pointer,
    mouse, wheel, keyboard, input, focus, touch, drag and clipboard
    fields, `target`/`currentTarget`, `preventDefault` and
    `stopPropagation`. Per-name event types need polymorphic record
    fields ([design-notes.md](design-notes.md)). Test
    `b19_b20_web_platform`.
20. **Missing declarations.** Canvas 2D (paths, styles, gradients,
    `measureText`, transforms), `devicePixelRatio`, `WebSocket`,
    `ResizeObserver`, `requestAnimationFrame`, `performance.now`,
    `localStorage`, `fetch`/`Response`/`Blob`/`URL.createObjectURL`,
    `navigator.mediaDevices.getUserMedia`, Web Audio (`AudioContext`,
    `AudioWorkletNode`, `MessagePort`, `AudioBuffer`, gain and analyser
    nodes), `WebAssembly.instantiate`/`Memory`, `Float32Array` and
    `Uint8Array` with `subarray`/`slice`/`set`/`buffer`, `String`'s
    `match`/`matchAll`/`search`/`at`/…, `Array.from`, `Object.entries`,
    `Object.values`, `Object.fromEntries`, and an AudioWorklet global scope
    (`--lib builtin:audioworklet`: `AudioWorkletProcessor`,
    `registerProcessor`, `sampleRate`, `currentTime`, `currentFrame`).
    Tests `b19_b20_web_platform`, `b20_core_additions`,
    `b20_audio_worklet`.
21. **`class … extends Base`.** A class may extend a declared class (a lib
    class included); the constructor calls `super(…)` first, and the
    instance is the base's fields and methods plus the subclass's.
    `super.method()` is rejected with an error that says so. Test
    `b21_class_extends`.

### E. Features

22. **Dictionaries: implemented.** `Dict<V>` and `{ [String]: V }`, object
    literals checked against it, `V | Undefined` reads,
    `Object.entries`/`values`/`fromEntries`; `Map<K, V>` and `Set<T>` in
    annotations. Test `b22_dict`.
23. **Newtypes: already there as `nominal type`.** Documented, with the
    identity-cast module Rosaclef already has; arithmetic lifting and
    array-index capabilities considered and not done (reasons in
    [design-notes.md](design-notes.md#newtypes--use-nominal-type)).
24. **Polymorphic record fields: rank-1, with a clearer error.** The error
    says what is generic and what to write instead. Golden
    `24-rank-1-field`.
