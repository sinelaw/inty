# Performance: checking a real module graph

This is a write-up of profiling and speeding up inty on
[Rosaclef](https://github.com/sinelaw/rosaclef)'s `web/`, a ~5.7k-line
vanilla-JS DAW frontend of 19 files (21 modules with its `.d.js`
declarations), and of the tools that came out of it: `--timings` and
checking several files in one run.

## Before and after

One `inty` process per module, four at a time on a 4-core machine,
`--lib types/newtypes.d.js --lib types/globals.d.js`, Rosaclef at
`4f88bd5` (branch `claude/affectionate-pascal-cxcj39`). "Before" is inty
with the bug fixes of the same round (the unmodified `1713277` stops within
3 s at the first `new Date()`, see [rosaclef-report.md](rosaclef-report.md),
so it never gets far enough to be slow) but none of the changes below; a
run was stopped after 25 minutes.

| Module (with its imports) | Before | After (4 at a time) | After (one at a time) |
|---|---:|---:|---:|
| src/main.js (entry) | > 1500 s | 1.99 s | 1.76 s |
| src/ui/shell.js | > 1500 s | 1.79 s | 1.61 s |
| src/ui/pianoroll.js | > 1500 s | 0.99 s | 0.91 s |
| src/ui/playlist.js | > 1500 s | 0.80 s | 0.72 s |
| src/keys.js | > 1500 s | 1.18 s | 0.94 s |
| src/ui/mixer.js | 717 s | 0.86 s | 0.77 s |
| src/ui/browser.js | 381 s | 0.54 s | 0.50 s |
| src/ui/rack.js | 375 s | 0.71 s | 0.59 s |
| src/ui/topbar.js | 306 s | 0.60 s | 0.51 s |
| src/audio.js | 115 s | 0.33 s | 0.28 s |
| src/ui/agent.js | 24.5 s | 0.53 s | 0.46 s |
| src/net.js | 22.6 s | 0.26 s | 0.25 s |
| src/ui/widgets.js | 13.0 s | 0.40 s | 0.35 s |
| test/tree.test.js | 5.1 s | 0.22 s | 0.19 s |
| src/ui/toast.js | 4.2 s | 0.29 s | 0.23 s |
| src/store.js | 3.0 s | 0.22 s | 0.19 s |
| src/model.js | 1.7 s | 0.17 s | 0.13 s |
| src/ui/tree.js | 1.1 s | 0.16 s | 0.14 s |
| src/ui/memory.js | 0.7 s | 0.12 s | 0.09 s |

The whole tree in one run, `inty --lib … src/*.js src/ui/*.js test/*.js`:
**1.5 s** (each of the 21 modules checked once).

## How it was profiled

`perf` isn't available in the environment this was done in, so the
profiles are stack samples taken with gdb (`thread apply all bt`, a few
dozen samples per run) of a release build with line tables
(`CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`), aggregated by function
(inclusive) and by the innermost inty frame. Coarse, but each of the
problems below showed up in a third to two thirds of the samples.

## What was slow

Each fix was measured on its own; the numbers are one process, one module.

1. **Speculation copied the inference state** (commit "Speculative
   unification without cloning the inference state"). `subsume`, `join`
   and `union_of` try a unification and roll it back on failure. The
   snapshot for that rollback cloned the whole substitution (deep copies
   of every bound type, the DOM's hundred-field rows included), the
   pending constraints and the set of number-kinded variables. Every
   attempt cost time in proportion to everything inferred so far, which
   made checking quadratic; it was over half of all samples. The
   substitution now keeps an undo trail, like the union-find table
   already did, and the constraints and number-kinded variables, which a
   speculative branch only adds to, are truncated on rollback.
   `browser.js` 331 s → 28 s, `audio.js` 133 s → 11 s.

2. **Extending the environment copied it**, and generalisation re-walked
   it. Every `let`, parameter and narrowing cloned both maps of the
   `TypeEnv`, deep-copying each binding's scheme, and every
   generalisation computed the free variables of every scheme in scope.
   The maps are now persistent (`im::HashMap`, bindings behind `Arc`),
   and each binding caches its free variables. `mixer.js` 52 s → 18 s,
   `net.js` 3.9 s → 0.9 s.

3. **Imported modules' leftover constraints piled up.** Rosaclef decodes
   `JSON.parse` results with generic decoders, and each call of one posts
   its property reads on a receiver that is never known: thousands of
   pending constraints. An imported module's leftovers weren't solved
   when it had been checked, so they were carried into every importer,
   and each generalisation there substituted all of them again. They are
   now solved when the module is done (numeric defaulting already was),
   which also puts their errors in the right file. `mixer.js` 18 s →
   1.9 s.

4. **Every import re-checked the module**, and transitively its imports:
   checking `main.js` loaded 909 modules for the 20 it depends on
   (`model.js` 164 times). Each importer also got its own copy of a
   module's mutable state, so two importers' conflicting uses of it went
   unnoticed. Modules are now checked once per run and shared.
   `main.js` 30 s → 1.3 s.

5. **Failed speculative unifications formatted their errors.** Every
   failed attempt built a diagnostic — pretty-printing both types and
   scanning the whole substitution for an "origin" label (which, for a
   concrete type, picked an unrelated variable bound to an equal type:
   the misleading "Found type: from parameter 'w'" labels in the report).
   The scan is gone, and errors raised inside a speculative attempt skip
   rendering.

The suspects the report listed, in these terms: many property reads on
one `JSON.parse` result — yes, item 3; big DOM rows unified repeatedly —
the cost was copying them (items 1 and 2), not unifying them; importers
re-checking dependencies — yes, item 4; quadratic row substitution — the
quadratic part was the substitution copy of item 1.

## `--timings`

`inty --timings file.js` prints to stderr each module's own checking time
(its imports excluded) and the twenty slowest top-level declarations:

```
Timings (each module's own time; imports excluded):
      193.2 ms  src/ui/pianoroll.js
      165.9 ms  src/ui/rack.js
      …
Slowest top-level declarations:
       90.8 ms  function studio  (src/ui/shell.js:29)
       80.2 ms  function browser  (src/ui/browser.js:104)
       …
```

A group of mutually recursive functions is one entry; a statement's time
excludes the function groups it triggered.

## Checking several files in one run

`inty a.js b.js …` checks each file, sharing one state: a module imported
by several of them — or itself given as a file — is checked once, and its
state is shared as at runtime. The summary says how many modules were
checked in all:

```
All checks passed: 19 files (21 modules checked, 16 as imports) in 1.45s
```

## Source snapshots

Each module's text is read once per run (the module cache), and
diagnostics render the text that was checked — the source map keeps it —
rather than re-reading the file, so a file edited during a run can't
produce a report that mixes versions. (`inty.json` and `package.json` are
read at each resolution.)

## Not done

- **An on-disk cache** keyed by content hash. The whole of Rosaclef
  checks in 1.5 s, of which loading the built-in declarations is about
  0.1 s; a cache would have to serialise schemes with their type
  variables, named types and source ranges, which isn't worth it at this
  size.
- **`opt-level = 3`**: about 8 % faster than the workspace's `"s"`, which
  is tuned for size (the WebAssembly build).
- **Within one module**, generalisation still scans the pending
  constraints; a module with thousands of never-resolved property reads
  would still be slow. Types are also still deep-copied when a variable is
  bound; sharing them (`Arc`) would help programs with very large rows.
