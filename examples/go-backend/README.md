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

Run `node bench.mjs` in this directory. It builds inty, translates and
builds each `*.js` file here, checks that the output is identical to
Node's, and reports the median wall-clock time of 5 runs.

| benchmark       | node    | inty → go | speedup | what it stresses                           |
| --------------- | ------: | --------: | ------: | ------------------------------------------ |
| `sieve`         | 1674 ms |    375 ms | 4.47x   | large `boolean[]`: 1 byte per element in Go |
| `array-hof`     | 1714 ms |    607 ms | 2.83x   | `map` / `filter` / `reduce` with closures  |
| `fib`           |  374 ms |    206 ms | 1.82x   | call overhead (naive recursion)            |
| `collatz`       | 3104 ms |   2157 ms | 1.44x   | `%` and `/` on integer-valued doubles      |
| `spectral-norm` |  657 ms |    586 ms | 1.12x   | numeric loops over `number[]`              |
| `nbody`         |  407 ms |    400 ms | 1.02x   | float arithmetic on object fields          |
| `mandelbrot`    |  877 ms |    891 ms | 0.98x   | pure float arithmetic in registers         |
| `particles`     |  353 ms |    368 ms | 0.96x   | many short-lived small objects (GC)        |

These numbers are from Node v22.22.2 and Go 1.24.7 on a 4-core linux/amd64
container. Node's startup alone (`node -e ""`) takes about 28 ms, and that
time is included in the Node column.

What the numbers show:

- **Big wins** come where V8 pays for being dynamic. It stores booleans
  in large arrays as tagged values, calls go through generic machinery,
  and callbacks passed to array built-ins go through calls it can't
  specialise as well.
- **Parity** comes on tight float loops such as `mandelbrot` and `nbody`.
  Once V8's optimising compiler has warmed up on monomorphic code, it
  produces machine code about as good as Go's. Static types don't buy
  much more there.
- **Allocation-heavy code** (`particles`) is also about even. V8's
  generational GC is very good at short-lived objects.

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
