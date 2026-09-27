# Benchmarks: inty → Go vs Node and Bun

This compares the Go translation produced by `inty go` with the original,
unmodified JavaScript running under **Node (V8)** and **Bun
(JavaScriptCore)**. The programs and the harness are in this directory;
see the [README](README.md) for what the backend supports.

**Summary.**
- **Memory:** the Go binary uses the least memory in all 16 benchmarks.
  It is typically ~10 MB against 40–60 MB, and up to 24x less than Node
  (`sieve`).
- **Speed vs Node:** Go is faster in 12 of the 16, by up to 31x
  (`array-hof`) and 9x (`particles`). The other 4 are level: their
  confidence intervals include 1.0. None is slower.
- **Speed vs Bun:** Go is faster in 13 and level in 3.
- **Closest to Node:** `mandelbrot` and `spectral-norm`, where a warm
  JIT emits the same machine code Go does, and `nbody`, which has one
  known cost left. [Closest to Node](#closest-to-node) has the
  measurements.

## Reproducing

```sh
cd examples/go-backend
node bench.mjs                    # all benchmarks, 10 processes per runtime
node bench.mjs --processes 3 fib  # a quick subset
node bench.mjs --json raw.json    # also dump every sample
```

It needs `node`, `go` (>= 1.22) and `python3`, which it uses for
`getrusage`. `bun` is optional; pass `--no-bun` to skip it. The harness
builds inty, translates and compiles every `*.js` here, and checks that
every runtime prints byte-identical output. A mismatch is flagged in the
table and makes the run exit non-zero.

## Methodology

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

## Programs

| benchmark | what it is |
| --- | --- |
| `raytracer` | Whitted ray tracer (spheres, shadows, reflections), 1280x960, with vector math on `{x, y, z}` objects |
| `orders` | ETL batch job over 1M synthetic orders: validate, enrich, aggregate by region and category, top customers |
| `bytecode-vm` | stack-based bytecode interpreter with switch dispatch, running a compiled prime counter |
| `log-analytics` | generate 35 MB of access logs, then parse them byte by byte and aggregate status codes, latency percentiles and path hits |
| `fuzzy-search` | spell-check suggestions: Levenshtein distance from 60 queries against a 20k-word dictionary |
| `dijkstra` | shortest paths on a 490k-node road grid in CSR form, with a hand-written binary heap |
| `dijkstra-typed` | the same program with the graph copied into `Int32Array`s, as performance-minded JavaScript would store it |
| `game-of-life` | Conway's Life on a 1024x1024 torus |
| `sieve`, `fib`, `collatz`, `array-hof`, `nbody`, `spectral-norm`, `mandelbrot`, `particles` | classic kernels, each isolating one effect |

## Results

These are from Node v22.22.2 (V8), Bun 1.3.11 (JavaScriptCore) and Go
1.24.7 on a 4-core linux/amd64 cloud container. Each runtime got 10
processes after 1 discarded, so 30 warm iterations. Every program's
output was byte-identical across all three. On their own, the runtimes
take 29 ms (Node) and 4.3 ms (Bun) to start.

**Steady state.** Warm iterations only, so JIT warm-up and startup are
excluded. Median ms (IQR). Speedup = JS time / Go time, with a 95% CI:

| benchmark | node warm | bun warm | inty → go warm | **vs node** [95% CI] | **vs bun** [95% CI] | output |
| --- | ---: | ---: | ---: | ---: | ---: | :---: |
| array-hof | 811 (783–872) | 178 (173–192) | 26.1 (24.2–30.9) | **31.11x** [26.62–33.48] | **6.83x** [5.81–7.22] | identical |
| bytecode-vm | 939 (888–964) | 274 (257–306) | 252 (238–286) | **3.73x** [3.25–3.94] | **1.09x** [0.95–1.21] | identical |
| collatz | 1555 (1452–1602) | 3301 (3224–3387) | 1035 (993–1059) | **1.50x** [1.44–1.55] | **3.19x** [3.10–3.27] | identical |
| dijkstra | 328 (309–347) | 352 (334–376) | 316 (296–335) | **1.04x** [0.98–1.11] | **1.11x** [1.04–1.19] | identical |
| dijkstra-typed | 276 (256–301) | 280 (265–289) | 254 (227–266) | **1.09x** [1.03–1.24] | **1.10x** [1.05–1.25] | identical |
| fib | 351 (331–372) | 244 (236–253) | 176 (146–183) | **2.00x** [1.87–2.41] | **1.39x** [1.34–1.68] | identical |
| fuzzy-search | 614 (576–653) | 377 (367–387) | 386 (357–399) | **1.59x** [1.49–1.72] | **0.98x** [0.94–1.05] | identical |
| game-of-life | 964 (901–982) | 874 (832–917) | 419 (398–443) | **2.30x** [2.18–2.38] | **2.09x** [1.99–2.21] | identical |
| log-analytics | 522 (484–648) | 477 (452–509) | 182 (167–194) | **2.87x** [2.65–3.44] | **2.63x** [2.41–2.87] | identical |
| mandelbrot | 832 (786–896) | 889 (837–922) | 867 (815–905) | **0.96x** [0.91–1.03] | **1.03x** [0.97–1.08] | identical |
| nbody | 374 (352–391) | 491 (461–512) | 391 (362–399) | **0.96x** [0.91–1.03] | **1.26x** [1.18–1.36] | identical |
| orders | 403 (377–438) | 631 (568–673) | 144 (130–164) | **2.79x** [2.57–3.03] | **4.37x** [3.81–4.75] | identical |
| particles | 256 (240–263) | 618 (597–639) | 28.3 (24.7–31.9) | **9.06x** [8.15–10.34] | **21.85x** [19.74–24.87] | identical |
| raytracer | 383 (366–418) | 442 (428–486) | 107 (96.6–119) | **3.56x** [3.28–3.96] | **4.11x** [3.81–4.68] | identical |
| sieve | 787 (744–815) | 330 (321–349) | 126 (121–145) | **6.23x** [5.43–6.59] | **2.62x** [2.29–2.79] | identical |
| spectral-norm | 552 (504–587) | 768 (712–789) | 539 (520–561) | **1.02x** [0.98–1.07] | **1.43x** [1.35–1.45] | identical |

**Whole process.** 4 iterations plus startup, median per process,
node / bun / go:

| benchmark | cold 1st iteration | wall | CPU (user+sys) | peak RSS |
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

## What the numbers say

- **Memory is the most consistent win.** The Go binary's peak RSS is
  lower in every benchmark. It is about 10 MB where the JS engines sit
  at 40–60 MB, and 10 MB vs 243 MB (Node) for `sieve`, whose
  `boolean[]` becomes a 1-byte-per-element `[]bool`.
- **Allocation-heavy code now wins the most.** Two changes remove the
  allocations that V8's and JavaScriptCore's young-generation GCs
  absorb and Go's collector doesn't:
  - `array-hof` fuses its `map`/`filter`/`reduce` chains into one loop.
  - `particles` stores its small `{x, y}` vectors as Go values instead
    of heap objects.
- **Record- and object-heavy code** (`orders`, `raytracer`) is 2.8–4.4x
  faster than both. Static types remove what both JITs have to discover
  and guard at runtime.
- **Integer-heavy code gains from `Int`.** `game-of-life`,
  `log-analytics` and `sieve` do index arithmetic, which is now Go
  `int` arithmetic (see [Integers](#integers-int-as-a-go-int)).
- **Array-heavy loops no longer lose.** `dijkstra` was 8% behind Node.
  It is now level with it (1.04x), and 1.09x ahead with its graph in
  `Int32Array`s (`dijkstra-typed`). See [What changed](#what-changed).
- **Ties:**
  - **Tight float loops** (`mandelbrot`, `spectral-norm`) tie with
    Node: once warm, a JIT emits the same machine code Go does.
  - **`nbody`** is level with Node within noise (0.96x, CI 0.91–1.03),
    but has one known cost left; see [Closest to Node](#closest-to-node).
  - **`bytecode-vm`** is 3.7x faster than Node but level with Bun. Its
    remaining cost is `%` on a `Number[]` stack (the program's own
    annotation), which Go computes on doubles. JavaScriptCore most
    likely keeps these whole-number values as 32-bit integers (as V8
    does with its Smis), but that isn't measured here.

## What changed

Profiles of the slowest programs, taken with Go's CPU profiler and
`GODEBUG=gctrace=1`, showed each time going to memory management rather
than computation. Three backend changes followed:

- **Array pipelines are fused.** `xs.map(f).filter(g).reduce(h, 0)`
  compiles to one loop with no intermediate arrays, when every callback
  is pure. The same holds when an intermediate sits in a `const` that is
  used once. In `array-hof` about 70% of the time had gone to zeroing,
  growing and collecting the throwaway arrays.
- **Small structs are values.** A struct type is a Go value, not a
  pointer, when two things hold:
  - no operation of the program at that type can tell a copy from the
    original: no field write, identity comparison, truth test,
    nullable type or recursion;
  - it takes at most 4 words.

  In `particles`, 62% of the CPU had gone to allocating vectors. The
  size limit exists because a large record in a growing array is copied
  whole every time the array grows. With 8-field `orders` records by
  value, the first iteration took 7x longer and peak memory tripled.
- **`new Array(n).fill(v)` is one allocation.** See fast-diff below.
- **A `switch` over literal `const`s is a jump table.** `bytecode-vm`
  dispatches on opcodes declared `const PUSH = 0`. Emitted as Go
  variables, the `switch` compiled to a chain of comparisons. `case`
  labels now use the constants' values, and Go builds a jump table: 430
  ms became 316 ms, level with Bun. The consts stay Go variables
  everywhere else, because Go folds constant expressions by its own
  rules (`1 / zero` is a compile error, not `Infinity`).

| benchmark | before (warm) | after (warm) | peak RSS before / after |
| --- | ---: | ---: | ---: |
| array-hof | 298 ms | 36.7 ms | 12 / 10 MB |
| particles | 386 ms | 33.8 ms | 10 / 10 MB |
| orders | 203 ms | 144 ms | 178 / 176 MB |
| raytracer | 185 ms | 130 ms | 10 / 10 MB |
| bytecode-vm | 452 ms | 316 ms | 10 / 10 MB |

The "before" column is the first published run (float64 numbers, before
these changes), and the "after" column the run that introduced each
change. The [Integers](#integers-int-as-a-go-int) section has
the `Int` change's share on its own.

**Array loops.** `dijkstra` was the last benchmark clearly behind Node.
A CPU profile put 42% of its time in the binary heap's sift-down loop,
and editing the generated Go one change at a time found the causes.
Three changes followed:

- **Loops keep array headers in locals.** An ordinary array is a Go
  `*[]T`. Go reloads the slice header after every store, because its
  optimiser can't tell that storing an element leaves the header
  unchanged. A loop now copies the header into a local once, when
  nothing in the loop can change it except the loop's own stores:
  - no calls (`Math.*` aside), closures or `new`;
  - the array's name is never reassigned in the loop, and appears only
    as `a[i]`, `a[i] = v` or `a.length`;
  - no store goes through any other path, such as `o.xs[i] = v`.

  A store that may grow the array hands back the new header. A store
  to an index the same iteration has already read is a plain store.
  The first version put that store in a helper function whose cost was
  81 against Go's inlining budget of 80. Every store became a call, and
  `dijkstra` took 434 ms. Stores are now written out inline.
- **`Math.floor(a / b)` on `Int`s is integer division.** It gives
  exactly the result of dividing in doubles whenever |a| and |b| are
  below 2^53 and b isn't 0.
- **`k * a` for a literal `k`** checks `|a| ≤ (2^53−1)/|k|` with
  integer compares instead of a double multiply.

Go only, run interleaved with the version before each step:

| step | dijkstra | dijkstra-typed |
| --- | ---: | ---: |
| before | 357–365 ms | — |
| integer division, literal-factor checks | 334 ms | 311 ms |
| array headers in loop locals | 306 ms | 251 ms |

`dijkstra-typed` also uses typed arrays, which inty now supports:
`Int32Array`, `Uint8Array` and `Float64Array` become Go slices of
`int32`, `uint8` and `float64`. A store wraps to 32 or 8 bits exactly
as JavaScript does. Both runtimes gain about as much from them (Node
328 → 276 ms, Go 316 → 254 ms in the results above). Node gets 4-byte
elements kept outside the heap its GC scans. Go gets the 4-byte
elements alone: its `[]int` holds no pointers, so its GC never scanned
it.

## Closest to Node

**`mandelbrot` and `spectral-norm`** are float loops with nothing to
allocate or check. Once warm, V8 emits the same machine code Go does.

**`nbody` (0.96x, CI 0.91–1.03)** is limited by `sqrt` and division
latency, which V8 pays too. Its one known extra cost is `bi.vx/vy/vz`:
three running sums that go through memory on every inner iteration.
Editing the generated Go (in an earlier, slower session: Node took
408–470 ms there):

| variant | warm |
| --- | ---: |
| as generated | 467 ms |
| slice header and masses hoisted into locals | 466 ms |
| `bi`'s fields kept in locals across the inner loop | **302 ms** |

Go can't keep them in registers, because `bj` might be the same object
as `bi`, and neither can inty: the types don't rule out an array
holding one object twice. A sound version would check `bi !== bj` once
per inner iteration and fall back when they are the same.

Node's small-integer arrays take 8 bytes per element like Go's `[]int`:
official Node builds don't enable V8's pointer compression, which would
make them 4 (measured).

## A real tool: md2html

[`tools/md2html.js`](tools/md2html.js) is a ~700-line Markdown → HTML
converter (CommonMark core plus GitHub tables and strikethrough) written
as ordinary JavaScript and reading and writing files through
`node:fs` / `node:process`. Unlike the programs above it isn't a loop
kernel with an in-process benchmark protocol: it's measured the way a
CLI is used, as **whole processes** — startup, reading the input,
converting, writing the HTML.

`node tools/bench.mjs` translates and builds it, checks that Node, Bun
and the Go binary produce byte-identical HTML, then runs each side 15
times per input (after one discarded warm-up round), interleaved in
random order. Wall time, CPU time (user + sys) and peak RSS come from
`getrusage`; medians are reported.

Inputs: the repository README (5.2 KB), and every Markdown file in the
repository concatenated and repeated to 20.5 MB.

| input | node | bun | inty → go | go vs node / bun | CPU node / bun / go | peak RSS node / bun / go |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small (5.2 KB) | 72.1 ms | 36.2 ms | 2.9 ms | **24.6x / 12.4x** | 76 / 42 / 3 ms | 58 / 44 / 10 MB |
| large (20.5 MB) | 1249 ms | 1126 ms | 605 ms | **2.06x / 1.86x** | 1638 / 2082 / 769 ms | 336 / 474 / 150 MB |

Node v22.22.2, Bun 1.3.11, Go 1.24.7, linux/amd64.

- **Small inputs are startup.** A native binary starts in ~3 ms; the JS
  engines spend 35–70 ms before running a line. For a tool invoked once
  per file — a build step, a pre-commit hook — this is the number that
  matters.
- **Large inputs are throughput.** Here the gap is 1.9–2.1x in wall
  time, with 53–63% less CPU (the engines' JIT and GC threads work in
  parallel with the program) and less than half the memory.
- The Go side's one runtime-level optimisation that mattered was sizing a
  string array's `join` once (`strings.Join`); the program builds its
  output by pushing strings onto an array and joining them, as idiomatic
  JavaScript does.

## A real library: fast-diff

[`tools/fastdiff.js`](tools/fastdiff.js) is a port of
[fast-diff](https://github.com/jhchen/fast-diff) 1.3.0, the npm package
(about 35M weekly downloads) that Quill uses for its text diffs. It is
the diff core of Neil Fraser's diff-match-patch: common prefix and suffix
stripping, the half-match speedup, Myers' O(ND) bisection, and the
merge and semantic-cleanup passes. It's wrapped in a CLI:
`fastdiff old.txt new.txt [--cleanup]`. The port keeps upstream's
functions and control flow. Its header comment lists every change the
subset forces, such as `{op, text}` records for `[op, text]` tuples and
character tests for regexes.

**Correctness.** Differential fuzzing (6,606 diffs, with and without
cleanup) compares it with the npm package: random strings over small
alphabets, and random insertions, deletions and moved blocks in the
repository's files. The op sequences are identical, and the Go binary
prints byte-identical output on all of them. Inputs are ASCII:
inty-go strings are byte strings, while JS strings are UTF-16.
`crates/inty-go/tests/go_backend.rs` pins the output on a realistic edit
and on three small inputs that reach the rarer cleanup paths.

`node tools/bench-fastdiff.mjs` translates and builds the tool, checks
that Node, Bun and the Go binary print byte-identical diffs, and then
measures as for md2html: whole processes, 21 interleaved runs per cell
after one discarded warm-up round, medians of wall time, CPU time
(user + sys) and peak RSS. All inputs are generated deterministically
(seeded PRNG) from the repository's own files:

- **small:** the README (5.2 KB) vs a copy with 6 edits;
- **large:** the first 2 MB of the Rust sources vs a copy with 40
  scattered insertions, deletions, replacements and moved blocks, diffed
  with and without `--cleanup`;
- **dense:** 100 KB of the same with 2,000 small edits (one every ~50
  characters). Here the half-match speedup rarely applies, so the Myers
  bisection does the work.

| input | node | bun | inty → go | go vs node / bun | CPU node / bun / go | peak RSS node / bun / go |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small (2 × 5 KB) | 109 ms | 65.0 ms | 12.5 ms | **8.7x / 5.2x** | 146 / 80 / 13 ms | 60 / 46 / 10 MB |
| large (2 × 2 MB) | 1072 ms | 1643 ms | 700 ms | **1.53x / 2.35x** | 1185 / 1689 / 757 ms | 217 / 245 / 86 MB |
| large, `--cleanup` | 1078 ms | 1634 ms | 701 ms | **1.54x / 2.33x** | 1178 / 1689 / 760 ms | 218 / 245 / 86 MB |
| dense (2 × 100 KB) | 563 ms | 947 ms | 345 ms | **1.63x / 2.75x** | 728 / 1011 / 362 ms | 72 / 64 / 10 MB |

Node v22.22.2, Bun 1.3.11 (default options, i.e. without `--smol`),
Go 1.24.7, linux/amd64.

- **Small inputs:** the native binary wins by 5–9x. The gap is smaller
  than for md2html because even a 5 KB diff runs a few bisections.
- **Large input:** Go is 1.5x faster than Node and 2.3x faster than
  Bun, at 40% of the memory.
  - Each bisection builds two arrays the size of both texts: about 4M
    elements at the top level, and hundreds of thousands in the
    recursive calls.
  - Building them with `push(-1)` in a loop made this input a test of
    allocating and page-faulting large arrays. Go lost it at 1.9 s and
    197 MB.
  - They are now built with `new Array(n).fill(-1)`, which inty types as
    an array (a `new Array(n)` alone can't be read: its holes would be
    `undefined`). The backend emits it as a single allocation.
  - That cut Go's allocation from 897 MB to 338 MB and its GC cycles
    from 45 to 26.
- **Dense input:** Myers bisection is character comparisons and index
  arithmetic on the V arrays. Go wins: 1.6x vs Node and 2.8x vs Bun, at
  a seventh of the memory.
- **The one change to the upstream code:** `fill` instead of a `push`
  loop. It is idiomatic JavaScript, and it is also 9% faster under Node
  and 19% under Bun, with the same memory.
- **What is left:** of Go's 86 MB peak, about 67 MB is the two
  top-level V arrays at 8 bytes per element. V8 stores the same values
  as 4-byte small integers. The bisection indices are integral and
  bounded by the input length, so a range analysis could make these
  arrays `[]int32` and bring the peak to about 53 MB.

## Integers: `Int` as a Go `int`

inty types a number with no fractional part as `Int`, a refinement of
`Number`: indices, `.length`, `indexOf`, loop counters, bitwise results
and `Math.floor`. The backend emits `Int` as a Go `int` and `Number` as a
`float64`. The conversion happens where an `Int` flows into a `Number`.
Indexing no longer goes through `int(float64)`, and integer `+ - %`
are single instructions.

Multiplication and `Math.floor`/`ceil`/`round`/`trunc` are checked:
past ±2^53, where doubles stop being exact, the program stops rather
than print something Node wouldn't. Each check is one double compare,
small enough for Go to inline. The first version, whose slow path built
an error message, wasn't inlined, which made `game-of-life`'s
`y * W + x` a call and the program 76% *slower*. A literal factor's
check is now a bound on the other operand, compared as integers, and
`Math.floor(a / b)` on `Int`s is integer division (see
[What changed](#what-changed)).

**Before/after, Go only.** The pre-`Int` binary (all numbers `float64`)
against the current one, run interleaved in the same session: 7
processes each, median of warm iterations. Node and Bun don't enter into
it, so drift of the machine between sessions doesn't either.

| benchmark | float64 | `Int` → `int` | change |
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

The programs that don't move are the float ones: mandelbrot and
raytracer compute in doubles throughout, and collatz's values need no
indexing. game-of-life gains most because its whole inner loop is
neighbour-index arithmetic. It goes from a tie with Node to 1.8x faster.

**md2html and fast-diff** (whole processes, as in their sections):

| program, input | float64 | `Int` → `int` | Go vs Node, before → after |
| --- | ---: | ---: | ---: |
| md2html, large (20 MB) | 1073 ms | 990 ms (CPU −16%) | 1.60x → 1.80x |
| fast-diff, large (4 MB) | 2022 ms | 1890 ms | 0.84x → 0.93x |
| fast-diff, large `--cleanup` | 1952 ms | 1769 ms | 0.88x → 0.98x |
| fast-diff, dense (200 KB) | 480 ms | 444 ms | 1.30x → 1.38x |

The fast-diff "after" column predates the inlining fix; a later, noisier
run with it had Go ahead of Node on the large input (1.15x). Peak memory
doesn't change: an `int` is 8 bytes, like a `float64`. The
large fast-diff input is still decided by allocating the V arrays, which
V8 stores as 4-byte integers. `[]int32` storage would need a range
analysis proving the values fit.

**Where Go and Node can still differ:** Int arithmetic that produces
`-0` in JS (`-0 * 1`) is `0` in Go, which only shows when it's printed
or divided by. An `Int` remainder by zero traps (JS gives `NaN`, which
isn't an `Int`).

