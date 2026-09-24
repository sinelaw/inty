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
literals whose shape inty inferred, `Math.*`, `performance.now()` and
`console.log`.

### I/O: Node's built-in modules

Programs read and write files, take arguments and set an exit status
through the same Node APIs they'd use anyway, imported from
`node:fs` and `node:process` (declared in
`crates/inty/stdlib/node/*.d.js`, so inty type-checks them too):

```js
import { readFileSync, writeFileSync, appendFileSync, existsSync } from "node:fs";
import process from "node:process";          // or { argv, exit, stdout, stderr }

const [input, output] = process.argv.slice(2);
const text = readFileSync(input, "utf8");      // stdin: readFileSync("/dev/stdin", "utf8")
writeFileSync(output, text.toUpperCase());
process.stderr.write("done\n");
process.exit(0);
```

`readFileSync` must be given the `"utf8"` encoding (it returns a string
only then). `process.argv` keeps Node's two leading entries, so
`argv.slice(2)` is the arguments on both sides. An I/O error ends the
program with a message and exit status 1, like an uncaught exception
in Node.

### A real tool: `md2html`

[`tools/md2html.js`](tools/md2html.js) is a ~700-line Markdown → HTML
converter (CommonMark core plus GitHub tables and strikethrough)
written as ordinary JavaScript: recursive string processing,
`slice`/`indexOf`/`charCodeAt`, arrays of lines, small records. It runs
under Node or Bun, and `inty go` turns it into a Go program with
byte-identical output (checked in `crates/inty-go/tests/go_backend.rs`).
On the repository's own Markdown files it matches
[markdown-it](https://github.com/markdown-it/markdown-it) exactly, except
for one file where markdown-it itself differs from the CommonMark
reference implementation.

```sh
inty go examples/go-backend/tools/md2html.js -o /tmp/md2html/main.go
cd /tmp/md2html && printf 'module md2html\n\ngo 1.22\n' > go.mod && go build -o md2html .
./md2html README.md -o README.html     # or: ./md2html - < in.md, --standalone
```

`node tools/bench.mjs` times the whole CLI process on a small document
(startup dominates) and a ~20 MB one (throughput dominates); see
[BENCHMARKS.md](BENCHMARKS.md#a-real-tool-md2html).

### Polymorphism: monomorphisation

inty infers polymorphic types, and the backend keeps them. A function
is emitted as **one Go function per concrete instantiation reachable
from `main`**, the way Rust and C++ compile generics:

```js
function first(xs) { return xs[0]; }
function getX(p) { return p.x; }          // any object with a numeric x
console.log(first([3, 1, 2]) + getX({ x: 1, y: 2 }));
console.log(first(["a", "b"]));
```

```go
func first(xs *[]float64) float64 { ... }
func first__2(xs *[]string) string { ... }
func getX(p *Obj1) float64 { ... }        // Obj1 is {x, y}
```

This covers the following. `tests/programs/polymorphism.js` exercises
all of it against Node:
- **Kinds of polymorphism:** parametric (`identity`, `first`),
  type-class (`twice(x) = x + x` on numbers and strings) and row
  (`getX` on differently shaped objects).
- **Higher-order and recursive functions:** user-defined higher-order
  functions, and recursion within a specialisation.
- **Other bindings:** polymorphic `const f = (…) => …` arrows, and
  polymorphic closures nested in other functions.
- **Nesting:** specialisations inside specialisations.

Functions nothing reaches are not emitted, and instantiations that map
to the same Go types share one copy.

How it works:
1. inty records, for every use of a polymorphic binding, which types
   replaced its quantified variables (`InferState::instantiations`).
2. The emitter requests a specialisation per distinct concrete choice.
3. It re-emits the function body with every recorded type substituted
   accordingly.

## Deliberate gaps

Anything outside the supported subset is reported as an "unsupported
construct" diagnostic at the source span. It is never silently
mistranslated.

- **Polymorphic values other than functions** (e.g. an object literal
  of polymorphic functions) used at a specific type are rejected, as are
  polymorphic `let` / `var` function values. Declare them with
  `function` or `const`.
- **Not supported:** `this`, classes, `new`, `try` / `throw`, getters and
  setters, spread, destructuring rest, `??`, `?.`, generic
  non-boolean `&&` / `||`, imports other than the Node built-ins above
  (programs are single files), and recursive object types.
- **Strings are treated as byte strings.** `.length` and indexing are
  exact only for ASCII (JS uses UTF-16 code units).
- **Out-of-bounds array reads panic**, where JS would return `undefined`.
  inty types `xs[i]` as the element type, so this is the same
  assumption the checker already makes. Writes past the end grow the
  array, as in JS.
- `console.log` takes one argument. It can't print whole arrays or
  objects, because Node's inspect formatting isn't reproduced.
