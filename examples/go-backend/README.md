# Go backend (proof of concept)

`inty go` takes a single-file JavaScript program that inty has fully
type-checked, and translates it into a standalone Go program. You build
the Go program with the regular Go compiler.

```sh
cargo build --release -p inty-cli
target/release/inty go examples/go-backend/nbody.js -o /tmp/nbody/main.go
cd /tmp/nbody && printf 'module nbody\n\ngo 1.22\n' > go.mod && go build -o nbody . && ./nbody
```

The JavaScript stays plain JavaScript. It still runs under Node unchanged,
and the benchmark harness checks that the Go binary prints exactly what
Node prints.

## Why this can be faster

V8 has to discover types at runtime. It uses hidden classes, inline
caches, speculative optimisation with deoptimisation guards, boxed or
tagged values, and a warm-up period. inty has already proved one static
type for every expression, so the Go backend can use plain machine
representations instead:

| JavaScript (as proven by inty) | Go                                        |
| ------------------------------ | ----------------------------------------- |
| `number`                       | `float64` in a register                   |
| `boolean[]`, `number[]`        | `*[]bool`, `*[]float64` (unboxed, dense)  |
| `{x: number, y: number}`       | `*Obj1` struct: fixed-offset field loads  |
| function                       | direct call (or a Go func value)          |
| closure passed to `.map`       | Go closure, with no megamorphic call site |

## Benchmarks

`node bench.mjs` (in this directory) does the following:
1. Builds inty.
2. Translates each `*.js` file here and builds it with `go build`.
3. Requires the Go binary's stdout to be identical to what Node (V8)
   prints, and to what Bun (JavaScriptCore) prints when Bun is installed.
4. Measures every side.

Pass `--processes N`, `--warmup W` and `--json out.json` for raw samples,
or benchmark names to run a subset. Pass `--no-bun` to skip Bun. It
needs `node`, `go` (>= 1.22) and `python3`, which it uses for
`getrusage`. `bun` is optional.

### Methodology

- **Steady state, not startup.** Every program ends with a small
  benchmark protocol: it runs its `main()` workload 4 times in one process
  and prints each iteration's `performance.now()` duration to stderr.
  Iteration 0 is *cold*; for the JS engines it includes JIT warm-up. Iterations 1–3
  are *warm*. The headline speedup uses warm iterations only, so neither
  runtime startup (Node ~30 ms, Bun ~4 ms) nor JIT warm-up counts
  against the JS engines.
- **Many interleaved processes.** Each side gets 10 fresh processes by
  default, after 1 discarded warm-up process, so 30 warm samples per side.
  Node, Bun and Go processes run in a random order every round, so drift
  (CPU frequency, noisy neighbours, page cache) affects every side equally.
- **Uncertainty.** Medians with interquartile ranges, and a 95% confidence
  interval on the speedup from a *cluster* bootstrap. Whole processes are
  resampled, because iterations within a process are correlated.
- **Resources.** For each process: cold first-iteration time, end-to-end
  wall time, CPU time (user + sys, including GC and JIT threads) and peak
  RSS.
- Each workload is long-running by itself (hundreds of milliseconds to
  about a second per iteration, with millions of hot-loop iterations), so
  timer resolution is irrelevant.

### Programs

| benchmark | what it is |
| --- | --- |
| `raytracer` | Whitted ray tracer (spheres, shadows, reflections), 1280x960, with vector math on `{x, y, z}` objects |
| `orders` | ETL batch job over 1M synthetic orders: validate, enrich, aggregate by region and category, top customers |
| `bytecode-vm` | stack-based bytecode interpreter with switch dispatch, running a compiled prime counter |
| `log-analytics` | generate 35 MB of access logs, then parse them byte by byte and aggregate status codes, latency percentiles and path hits |
| `fuzzy-search` | spell-check suggestions: Levenshtein distance from 60 queries against a 20k-word dictionary |
| `dijkstra` | shortest paths on a 490k-node road grid in CSR form, with a hand-written binary heap |
| `game-of-life` | Conway's Life on a 1024x1024 torus |
| `sieve`, `fib`, `collatz`, `array-hof`, `nbody`, `spectral-norm`, `mandelbrot`, `particles` | classic kernels, each isolating one effect |

### Results

*Preliminary* (calibration runs: warm iterations from a single process
per side; the full statistical run replaces this table). Node v22.22.2
vs Go 1.24.7, 4-core linux/amd64 container.

| benchmark | node warm | go warm | speedup | peak RSS node / go |
| --- | ---: | ---: | ---: | ---: |
| sieve | 743 ms | 176 ms | ~4.2x | 187 / 11 MB |
| array-hof | 840 ms | 285 ms | ~2.9x | — |
| bytecode-vm | 940 ms | 453 ms | ~2.1x | 50 / 10 MB |
| raytracer | 384 ms | 194 ms | ~2.0x | 53 / 10 MB |
| orders | 423 ms | 224 ms | ~1.9x | 471 / 236 MB |
| fib | 311 ms | 172 ms | ~1.8x | 50 / 10 MB |
| fuzzy-search | 639 ms | 411 ms | ~1.6x | 55 / 10 MB |
| log-analytics | 705 ms | 510 ms | ~1.4x | 270 / 163 MB |
| collatz | 1396 ms | 1002 ms | ~1.4x | — |
| game-of-life | 938 ms | 925 ms | ~1.0x | 104 / 10 MB |
| mandelbrot | 844 ms | 890 ms | ~0.95x | — |
| nbody | 370 ms | 422 ms | ~0.9x | — |
| spectral-norm | 533 ms | 603 ms | ~0.9x | — |
| dijkstra | 282 ms | 382 ms | ~0.75x | 168 / 83 MB |
| particles | 236 ms | 368 ms | ~0.65x | — |

## What's supported

Top-level and nested functions, closures, arrow functions, `let` /
`const` / `var`, and all loops except `for-in`. Also: labels, `switch`
with fall-through, numbers with exact JS formatting and `%` / bitwise
semantics, strings (ASCII), arrays (with the common methods), object
literals whose shape inty inferred, `Math.*` and `console.log`.

## Deliberate gaps

Anything outside the supported subset is reported as an "unsupported
construct" diagnostic at the source span. It is never silently
mistranslated.

- **Monomorphic programs only.** inty normally generalises
  `function id(x)` to `<a>(a) => a`. For the Go backend, let-polymorphism
  is switched off, so every binding gets exactly one type. Using one
  function at two types is a type error. Monomorphisation would lift
  this.
- **Not supported:** `this`, classes, `new`, `try` / `throw`, getters and
  setters, spread, destructuring rest, `??`, `?.`, generic
  non-boolean `&&` / `||`, ES modules, and recursive object types.
- **Strings are treated as byte strings.** `.length` and indexing are
  exact only for ASCII (JS uses UTF-16 code units).
- **Out-of-bounds array reads panic**, where JS would return `undefined`.
  inty types `xs[i]` as the element type, so this is the same
  assumption the checker already makes. Writes past the end grow the
  array, as in JS.
- `console.log` takes one argument. It can't print whole arrays or
  objects, because Node's inspect formatting isn't reproduced.
