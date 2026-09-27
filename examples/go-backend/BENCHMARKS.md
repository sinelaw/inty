# Benchmarks: inty → Go vs Node and Bun

`inty go` turns type-checked JavaScript into Go. This page compares the
Go program with the same, unchanged JavaScript running in **Node** (V8)
and **Bun** (JavaScriptCore).

## TL;DR

- **Memory: 2x to 24x less than Node, and 1.8x to 22x less than Bun.**
  Typically about 5x less than Node and 4x less than Bun: around 10 MB
  where they use 40–60 MB.
- **Speed: 2.5x faster than Node and 2.2x faster than Bun on average**
  over the 16 programs. By kind of code:

  | kind of code | vs Node | vs Bun |
  | --- | ---: | ---: |
  | allocation-heavy | 16.8x | 12.2x |
  | objects and records | 3.2x | 4.2x |
  | integers and arrays | 2.1x | 1.6x |
  | floating-point math | 1.0x (tie) | 1.2x |
  | real tools, large inputs | 1.6x | 2.2x |
  | real tools, small inputs | 14.7x | 8.3x |

  Averages are geometric means. Allocation-heavy: `array-hof`,
  `particles`. Objects and records: `orders`, `raytracer`. Floating-point:
  `mandelbrot`, `spectral-norm`, `nbody`. Integers and arrays: the other
  9 programs. Real tools: md2html and fast-diff, whole processes.

More detail:
- **Go is never clearly slower.** It beats Node on 12 of 16 programs and
  ties on the other 4. Against Bun: 13 wins, 3 ties.
- **The biggest wins come from not allocating:** 31x faster than Node on
  array pipelines (`array-hof`), 9x on code full of small objects
  (`particles`).
- **The ties:** three floating-point loops (`mandelbrot`,
  `spectral-norm`, `nbody`), where Node's JIT makes the same machine
  code Go does, and `dijkstra` (Go 4% ahead, within noise).
- **Small inputs are mostly startup:** a Go binary starts in about 3 ms,
  Node in about 30. That's the 14.7x for the real tools on small inputs.
- **The biggest memory gap** is `sieve`, 10 MB against Node's 243 MB. The
  smallest is `dijkstra-typed`, 89 MB against 207 MB.
- All three print exactly the same output for every program.

## Running them

```sh
cd examples/go-backend
node bench.mjs                    # all programs, 10 processes per runtime
node bench.mjs --processes 3 fib  # a quick run of one program
node bench.mjs --json raw.json    # also save every measurement
```

You need `node`, `go` (1.22 or later) and `python3`. `bun` is optional
(`--no-bun` skips it). The script builds inty, translates and compiles
each program, and fails if the three runtimes print different output.

## How we measure

- **Warm runs only.** Each program does its work 4 times in one
  process. The first run includes the JIT warming up; we report the
  other 3. So Node's and Bun's startup and warm-up don't count against
  them.
- **Many processes, in random order.** Each runtime gets 10 fresh
  processes (after 1 thrown away), shuffled so machine noise hits all
  three equally.
- **Medians, with error bars.** Each speedup comes with a 95%
  confidence interval, from resampling whole processes. If the interval
  includes 1.0, we call it a tie.
- Each run takes hundreds of milliseconds, so timer precision doesn't
  matter.

## The programs

| program | what it does |
| --- | --- |
| `raytracer` | ray tracer (spheres, shadows, reflections), 1280x960, with `{x, y, z}` vector objects |
| `orders` | batch job over 1M orders: validate, enrich, group by region and category, top customers |
| `bytecode-vm` | a small bytecode interpreter (a `switch` per instruction) running a prime counter |
| `log-analytics` | writes 35 MB of access logs, then parses them byte by byte into statistics |
| `fuzzy-search` | spelling suggestions: edit distance from 60 words to a 20k-word dictionary |
| `dijkstra` | shortest paths on a 490k-node road grid, with a hand-written heap |
| `dijkstra-typed` | the same, with the graph stored in `Int32Array`s |
| `game-of-life` | Conway's Life on a 1024x1024 grid |
| `sieve`, `fib`, `collatz`, `array-hof`, `nbody`, `spectral-norm`, `mandelbrot`, `particles` | classic small benchmarks, each testing one thing |

## Results

Node 22.22.2, Bun 1.3.11 and Go 1.24.7, on a 4-core Linux cloud
machine. On their own, Node takes 29 ms to start and Bun 4 ms.

**Speed.** Median of the warm runs. "vs node" is Node's time divided by
Go's, with the 95% interval in brackets:

| program | node | bun | inty → go | vs node | vs bun |
| --- | ---: | ---: | ---: | ---: | ---: |
| array-hof | 811 ms | 178 ms | 26.1 ms | 31.11x [26.62–33.48] | 6.83x [5.81–7.22] |
| bytecode-vm | 939 ms | 274 ms | 252 ms | 3.73x [3.25–3.94] | 1.09x [0.95–1.21] |
| collatz | 1555 ms | 3301 ms | 1035 ms | 1.50x [1.44–1.55] | 3.19x [3.10–3.27] |
| dijkstra | 328 ms | 352 ms | 316 ms | 1.04x [0.98–1.11] | 1.11x [1.04–1.19] |
| dijkstra-typed | 276 ms | 280 ms | 254 ms | 1.09x [1.03–1.24] | 1.10x [1.05–1.25] |
| fib | 351 ms | 244 ms | 176 ms | 2.00x [1.87–2.41] | 1.39x [1.34–1.68] |
| fuzzy-search | 614 ms | 377 ms | 386 ms | 1.59x [1.49–1.72] | 0.98x [0.94–1.05] |
| game-of-life | 964 ms | 874 ms | 419 ms | 2.30x [2.18–2.38] | 2.09x [1.99–2.21] |
| log-analytics | 522 ms | 477 ms | 182 ms | 2.87x [2.65–3.44] | 2.63x [2.41–2.87] |
| mandelbrot | 832 ms | 889 ms | 867 ms | 0.96x [0.91–1.03] | 1.03x [0.97–1.08] |
| nbody | 374 ms | 491 ms | 391 ms | 0.96x [0.91–1.03] | 1.26x [1.18–1.36] |
| orders | 403 ms | 631 ms | 144 ms | 2.79x [2.57–3.03] | 4.37x [3.81–4.75] |
| particles | 256 ms | 618 ms | 28.3 ms | 9.06x [8.15–10.34] | 21.85x [19.74–24.87] |
| raytracer | 383 ms | 442 ms | 107 ms | 3.56x [3.28–3.96] | 4.11x [3.81–4.68] |
| sieve | 787 ms | 330 ms | 126 ms | 6.23x [5.43–6.59] | 2.62x [2.29–2.79] |
| spectral-norm | 552 ms | 768 ms | 539 ms | 1.02x [0.98–1.07] | 1.43x [1.35–1.45] |

**Whole process.** All 4 runs plus startup, per process: Node / Bun /
Go.

| program | first run | wall time | CPU time | peak memory |
| --- | ---: | ---: | ---: | ---: |
| array-hof | 850 / 215 / 25.4 ms | 3281 / 780 / 110 ms | 3323 / 1001 / 116 ms | 132 / 59 / 10 MB |
| bytecode-vm | 941 / 254 / 264 ms | 3771 / 1101 / 1030 ms | 3742 / 1110 / 1021 ms | 51 / 41 / 10 MB |
| collatz | 1431 / 3021 / 1028 ms | 6026 / 12936 / 4076 ms | 5960 / 12785 / 4068 ms | 51 / 40 / 10 MB |
| dijkstra | 370 / 340 / 318 ms | 1579 / 1614 / 1463 ms | 1630 / 1711 / 1592 ms | 194 / 145 / 79 MB |
| dijkstra-typed | 335 / 278 / 228 ms | 1381 / 1339 / 1158 ms | 1442 / 1433 / 1221 ms | 207 / 162 / 89 MB |
| fib | 361 / 249 / 183 ms | 1483 / 992 / 702 ms | 1444 / 983 / 701 ms | 51 / 37 / 10 MB |
| fuzzy-search | 617 / 387 / 382 ms | 2483 / 1525 / 1510 ms | 2502 / 1567 / 1500 ms | 64 / 53 / 10 MB |
| game-of-life | 980 / 935 / 449 ms | 3879 / 3558 / 1703 ms | 3879 / 3571 / 1728 ms | 185 / 123 / 13 MB |
| log-analytics | 739 / 573 / 225 ms | 2521 / 2047 / 793 ms | 4362 / 2794 / 933 ms | 537 / 511 / 113 MB |
| mandelbrot | 874 / 908 / 841 ms | 3461 / 3575 / 3401 ms | 3423 / 3520 / 3367 ms | 53 / 39 / 10 MB |
| nbody | 384 / 515 / 400 ms | 1551 / 2005 / 1566 ms | 1545 / 2001 / 1535 ms | 53 / 41 / 10 MB |
| orders | 518 / 687 / 205 ms | 1827 / 2609 / 671 ms | 2691 / 2859 / 904 ms | 558 / 343 / 190 MB |
| particles | 328 / 634 / 30.4 ms | 1143 / 2526 / 124 ms | 1141 / 4729 / 117 ms | 84 / 46 / 10 MB |
| raytracer | 455 / 577 / 111 ms | 1668 / 1976 / 438 ms | 1708 / 2603 / 435 ms | 57 / 53 / 10 MB |
| sieve | 810 / 438 / 146 ms | 3282 / 1460 / 573 ms | 3435 / 1514 / 597 ms | 243 / 215 / 10 MB |
| spectral-norm | 618 / 797 / 528 ms | 2277 / 3087 / 2124 ms | 2276 / 3077 / 2117 ms | 55 / 43 / 10 MB |

## Why Go wins where it does

- **Memory.** There's no JIT and no large heap to fill, so most programs
  stay near 10 MB. `sieve`'s `boolean[]` becomes one byte per element:
  10 MB against Node's 243 MB.
- **Fewer allocations.** The biggest wins come from not allocating:
  - `array-hof`: `xs.map(f).filter(g).reduce(h)` becomes one loop with
    no temporary arrays.
  - `particles`: small `{x, y}` objects are stored as plain values
    instead of separate heap objects.
- **Types known in advance.** `orders` and `raytracer` are 2.8–4.4x
  faster than both engines. Nothing has to be discovered or checked
  while running.
- **Whole numbers as integers.** inty knows which numbers are always
  whole and makes them Go integers. That speeds up index-heavy code
  like `game-of-life`, `log-analytics` and `sieve` (see
  [Integers](#integers)).
- **`bytecode-vm`** is 3.7x faster than Node but ties Bun. Its stack is
  declared `Number[]`, so Go computes `%` on floating-point numbers. Bun
  probably keeps them as integers, but we haven't measured that.

## What we changed to get here

Each change came from profiling a slow program. "Before" is the first
published run; "after" is the run that added the change.

| change | program | before | after |
| --- | --- | ---: | ---: |
| array pipelines become one loop | `array-hof` | 298 ms | 36.7 ms |
| small objects stored as values | `particles` | 386 ms | 33.8 ms |
| … but only if at most 4 words | `orders` | 203 ms | 144 ms |
| | `raytracer` | 185 ms | 130 ms |
| `switch` on constants becomes a jump table | `bytecode-vm` | 452 ms | 316 ms |

- **One loop for a pipeline** only when every callback is pure. In
  `array-hof`, 70% of the time had gone to creating and freeing
  temporary arrays.
- **Objects as values** only when the program can't tell a copy from
  the original: no field writes, identity checks, `null` or recursion.
  Big records got slower as values, because a growing array copies them
  in full: `orders`' first run took 7x longer, with 3x the memory.
  Hence the 4-word limit.
- **`new Array(n).fill(v)`** is a single allocation (see
  [fast-diff](#a-real-library-fast-diff)).
- **Jump tables:** `bytecode-vm` switches on constants like
  `const PUSH = 0`. The `case` labels now use their values, so Go jumps
  straight to the right case instead of comparing one by one.

### Array loops (`dijkstra`)

`dijkstra` was the last program clearly slower than Node, by 8%. A
profile put 42% of its time in the heap code. Three changes fixed it:

- **Loops keep the array in a local variable.** A JavaScript array is a
  pointer to a Go slice. Go re-reads the slice through the pointer after
  every write, because it can't prove the write didn't change it. A
  loop now reads it once, if nothing in the loop could change it:
  - no function calls (`Math.*` is fine);
  - the array variable isn't reassigned in the loop;
  - the array isn't written through any other name.

  A write that might grow the array updates the local copy.
- **Integer division.** `Math.floor(a / b)` on integers uses Go's integer
  division. It gives exactly JavaScript's result for integers below
  2^53.
- **Cheaper overflow checks** when multiplying by a constant, as in
  `2 * i`.

A pitfall along the way: the first version put each write in a helper
function that was one point over Go's inlining limit. Every write became
a function call, and `dijkstra` got slower (434 ms). Writes are now
spelled out inline.

Go only, each step timed against the one before:

| step | `dijkstra` | `dijkstra-typed` |
| --- | ---: | ---: |
| before | 357–365 ms | — |
| integer division, cheaper checks | 334 ms | 311 ms |
| array in a local variable | 306 ms | 251 ms |

`dijkstra-typed` stores its graph in `Int32Array`s. inty now supports
`Int32Array`, `Uint8Array` and `Float64Array`: they become Go slices of
4-, 1- or 8-byte numbers, and writes wrap around exactly as in
JavaScript. They make Node 16% faster and Go 20% faster.

## Closest to Node

- **`mandelbrot` and `spectral-norm`** are plain floating-point loops.
  Once warm, Node's JIT emits the same machine code as Go.
- **`nbody`** (0.96x, a tie) mostly waits on square roots and
  divisions, which cost the same everywhere. One thing Go could do
  better: the sums `bi.vx`, `bi.vy`, `bi.vz` are written to memory on
  every inner step. Keeping them in variables made Go much faster in a
  hand-edited test: 467 → 302 ms, when Node took 408–470 ms. But that's
  only correct if `bj` is never the same object as `bi`, and the types
  can't promise that. A safe version would check `bi !== bj` and fall
  back when they're equal.

Node stores arrays of small integers at 8 bytes per element, just like
Go's `[]int`. (V8 has a "pointer compression" mode that would make them
4 bytes, but official Node builds turn it off. We checked.)

## A real tool: md2html

[`tools/md2html.js`](tools/md2html.js) is a 700-line Markdown-to-HTML
converter written as ordinary JavaScript, reading and writing files with
`node:fs`. We time it like a real command: whole processes, including
startup, reading the input and writing the HTML.

`node tools/bench.mjs` builds it, checks that all three produce the same
HTML, and runs each 15 times per input, in random order. The inputs are
the README (5.2 KB), and all of the repository's Markdown repeated to
20.3 MB.

| input | node | bun | inty → go | go vs node / bun | CPU node / bun / go | memory node / bun / go |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small (5.2 KB) | 77.0 ms | 38.1 ms | 3.0 ms | 25.3x / 12.5x | 77 / 44 / 3 ms | 58 / 44 / 10 MB |
| large (20.3 MB) | 1177 ms | 1165 ms | 625 ms | 1.88x / 1.86x | 1607 / 2050 / 792 ms | 335 / 453 / 142 MB |

- **On a small input, startup is everything.** Go starts in about 3 ms;
  Node and Bun take 35–75 ms before running any code. For a tool run
  once per file, this is what you notice.
- **On a large input,** Go is 1.9x faster, with half the CPU time (the
  engines' JIT and garbage collector run on other threads) and less
  than half the memory.
- The one runtime fix that mattered: joining the output strings in a
  single step (`strings.Join`).

## A real library: fast-diff

[`tools/fastdiff.js`](tools/fastdiff.js) is a port of the
[fast-diff](https://github.com/jhchen/fast-diff) npm package (about 35M
downloads a week; the Quill editor uses it). It keeps the original's
functions and logic. Its header comment lists what had to change for
inty, such as `{op, text}` records instead of `[op, text]` pairs.

**Is it correct?** We compared it with the npm package on 6,606 random
diffs, and every result matched, in Node and in Go. The inputs are
ASCII: inty-go strings are bytes, while JavaScript strings are UTF-16.

`node tools/bench-fastdiff.mjs` builds it, checks that the outputs match,
and runs each case 21 times. The inputs come from the repository's own
files:
- **small:** the README vs a copy with 6 edits;
- **large:** 2 MB of Rust source vs a copy with 40 scattered edits, with
  and without `--cleanup`;
- **dense:** 100 KB with 2,000 small edits, which forces the slow core
  algorithm (Myers' diff).

| input | node | bun | inty → go | go vs node / bun | CPU node / bun / go | memory node / bun / go |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small (2 × 5 KB) | 100 ms | 64.8 ms | 11.8 ms | 8.5x / 5.5x | 134 / 78 / 13 ms | 59 / 46 / 10 MB |
| large (2 × 2 MB) | 1025 ms | 1468 ms | 683 ms | 1.50x / 2.15x | 1167 / 1499 / 728 ms | 222 / 228 / 86 MB |
| large, `--cleanup` | 1007 ms | 1491 ms | 670 ms | 1.50x / 2.23x | 1140 / 1541 / 718 ms | 222 / 227 / 86 MB |
| dense (2 × 100 KB) | 522 ms | 860 ms | 320 ms | 1.63x / 2.69x | 664 / 915 / 335 ms | 72 / 66 / 10 MB |

- **Small:** 5–9x faster. The gap is smaller than md2html's because
  even a small diff does real work.
- **Large:** 1.5x faster than Node and 2.2x faster than Bun, with 40% of
  Node's memory. Most of the work is creating two big arrays (4 million
  elements) per step. Building them with `new Array(n).fill(-1)` instead
  of a `push` loop makes each one a single allocation. That's the only
  change to the original code, and it makes Node 9% faster and Bun 19%
  faster too.
- **Dense:** 1.6x faster than Node and 2.7x faster than Bun, with a
  seventh of the memory.
- **Room left:** most of Go's 86 MB is those two arrays, at 8 bytes per
  element. `Int32Array`s would halve that, but would change the port.
  Its main loops also miss the array-loop speedup above, because they
  call `text.charAt(i)`.

## Integers

inty types numbers that are always whole as `Int`: indices, `.length`,
loop counters, bitwise results, `Math.floor`. Go gets an `int` for these
and a `float64` for everything else. So indexing needs no conversion,
and integer `+`, `-` and `%` are single instructions.

JavaScript numbers are only exact up to 2^53. Multiplication and
`Math.floor`, `ceil`, `round` and `trunc` can go past that, so they're
checked: if a result gets too big, the Go program stops rather than
print a different answer from Node. Each check is one comparison. (An
early version of the check didn't inline, and made `game-of-life` 76%
slower.)

**Before and after `Int`, Go only.** Same session, 7 processes each:

| program | `float64` only | with `Int` | change |
| --- | ---: | ---: | ---: |
| array-hof | 430 ms | 335 ms | −22% |
| bytecode-vm | 694 ms | 483 ms | −31% |
| collatz | 1415 ms | 1427 ms | +1% (noise) |
| dijkstra | 574 ms | 526 ms | −8% |
| fib | 303 ms | 255 ms | −16% |
| fuzzy-search | 647 ms | 509 ms | −21% |
| game-of-life | 1177 ms | 683 ms | **−42%** |
| log-analytics | 342 ms | 261 ms | −24% |
| mandelbrot | 1472 ms | 1490 ms | +1% (noise) |
| nbody | 661 ms | 508 ms | −23% |
| orders | 264 ms | 220 ms | −17% |
| particles | 632 ms | 600 ms | −5% |
| raytracer | 304 ms | 305 ms | 0% |
| sieve | 252 ms | 215 ms | −15% |
| spectral-norm | 1117 ms | 924 ms | −17% |

Programs that compute in floating point (`mandelbrot`, `raytracer`) and
`collatz` don't change. `game-of-life` gains most: its inner loop is all
index arithmetic.

The same change on the real tools (whole processes):

| program, input | `float64` only | with `Int` | change |
| --- | ---: | ---: | ---: |
| md2html, large | 1073 ms | 990 ms | −8% |
| fast-diff, large | 2022 ms | 1890 ms | −7% |
| fast-diff, large `--cleanup` | 1952 ms | 1769 ms | −9% |
| fast-diff, dense | 480 ms | 444 ms | −8% |

Memory doesn't change: an `int` takes 8 bytes, like a `float64`.

**Where Go and Node can still differ:**
- An integer result that is `-0` in JavaScript (`Math.ceil(-0.5)`,
  `-0 * 1`) is `0` in Go. It only shows when printed or divided by.
- An integer `% 0` stops the program. JavaScript gives `NaN`, which
  isn't an integer.
- Adding integers isn't checked against 2^53, so a sum past it can
  differ from JavaScript's rounded result.
