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

**Full results, methodology and analysis:
[BENCHMARKS.md](BENCHMARKS.md).**

`node bench.mjs` translates and builds every `*.js` program here, checks
that the Go binary prints exactly what Node and Bun print, and measures
steady-state speed, CPU time and peak memory. Only warm iterations count,
from 30 samples per runtime in interleaved processes, with 95% confidence
intervals.

Headline numbers (steady-state speedup of the Go translation; >1 means
Go is faster):

| benchmark | vs Node (V8) | vs Bun (JSC) | peak RSS node / bun / go |
| --- | ---: | ---: | ---: |
| orders (ETL over 1M records) | 1.95x | 3.10x | 561 / 359 / 178 MB |
| raytracer | 2.07x | 2.43x | 57 / 52 / 10 MB |
| sieve | 3.99x | 1.64x | 210 / 186 / 11 MB |
| fib | 2.09x | 1.39x | 51 / 37 / 10 MB |
| array-hof | 2.80x | 0.57x | 131 / 61 / 12 MB |
| mandelbrot | 1.00x | 1.02x | 53 / 39 / 10 MB |
| particles | 0.66x | 1.57x | 85 / 46 / 10 MB |

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
