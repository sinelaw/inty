# Benchmarks: inty → Go vs Node and Bun

This compares the Go translation produced by `inty go` with the original,
unmodified JavaScript running under **Node (V8)** and **Bun
(JavaScriptCore)**. The programs and the harness are in this directory;
see the [README](README.md) for what the backend supports.

**Summary.**
- **Memory:** the Go binary uses the least memory in all 15 benchmarks.
  It is typically ~10 MB against 40–60 MB, and up to 16x less than Node
  (`game-of-life`, `sieve`).
- **Speed vs both engines:** it is clearly faster than Node and Bun in 9
  of the 15 benchmarks, by up to 21x (`array-hof`) and 15x
  (`particles`). Both of those used to be losses; see
  [What changed](#what-changed).
- **Speed vs Node:** it is faster than Node in 11 and ties in 2 more.
- **Losses:** `dijkstra` and `nbody` are ~10% slower than Node.
  [Where Go still loses](#where-go-still-loses) has the measured
  causes.

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
| `game-of-life` | Conway's Life on a 1024x1024 torus |
| `sieve`, `fib`, `collatz`, `array-hof`, `nbody`, `spectral-norm`, `mandelbrot`, `particles` | classic kernels, each isolating one effect |

## Results

These are from Node v22.22.2 (V8), Bun 1.3.11 (JavaScriptCore) and Go
1.24.7 on a 4-core linux/amd64 cloud container. Each runtime got 10
processes after 1 discarded, so 30 warm iterations. Every program's
output was byte-identical across all three. On their own, the runtimes
take 28 ms (Node) and 3.2 ms (Bun) to start.

**Steady state.** Warm iterations only, so JIT warm-up and startup are
excluded. Median ms (IQR). Speedup = JS time / Go time, with a 95% CI:

| benchmark | node warm | bun warm | inty → go warm | **vs node** [95% CI] | **vs bun** [95% CI] | output |
| --- | ---: | ---: | ---: | ---: | ---: | :---: |
| array-hof | 780 (764–791) | 179 (158–193) | 36.7 (29.9–43.4) | **21.24x** [18.58–23.44] | **4.87x** [4.08–5.37] | identical |
| bytecode-vm | 993 (986–1018) | 316 (306–341) | 316 (312–318) | **3.14x** [3.12–3.22] | **1.00x** [0.98–1.08] | identical |
| collatz | 1805 (1787–1819) | 4057 (4042–4081) | 1134 (1126–1151) | **1.59x** [1.58–1.61] | **3.58x** [3.56–3.61] | identical |
| dijkstra | 334 (323–345) | 358 (354–365) | 362 (359–366) | **0.92x** [0.91–0.94] | **0.99x** [0.98–1.00] | identical |
| fib | 408 (404–411) | 297 (294–304) | 225 (224–231) | **1.81x** [1.77–1.83] | **1.32x** [1.29–1.36] | identical |
| fuzzy-search | 710 (704–719) | 429 (426–434) | 429 (425–445) | **1.66x** [1.60–1.68] | **1.00x** [0.97–1.01] | identical |
| game-of-life | 1096 (1058–1121) | 1057 (1054–1077) | 561 (557–567) | **1.95x** [1.89–1.97] | **1.88x** [1.88–1.91] | identical |
| log-analytics | 562 (464–604) | 551 (522–588) | 195 (190–216) | **2.88x** [2.42–3.00] | **2.82x** [2.68–2.94] | identical |
| mandelbrot | 1145 (1139–1152) | 1164 (1161–1173) | 1127 (1123–1132) | **1.02x** [1.01–1.02] | **1.03x** [1.03–1.04] | identical |
| nbody | 415 (410–418) | 571 (567–578) | 469 (467–475) | **0.88x** [0.87–0.89] | **1.22x** [1.21–1.23] | identical |
| orders | 379 (364–428) | 707 (669–745) | 144 (133–163) | **2.62x** [2.51–2.74] | **4.89x** [4.70–5.09] | identical |
| particles | 275 (271–279) | 503 (495–522) | 33.8 (32.4–35.4) | **8.15x** [7.79–8.51] | **14.89x** [14.23–15.67] | identical |
| raytracer | 365 (359–368) | 443 (439–453) | 130 (130–134) | **2.79x** [2.73–2.82] | **3.39x** [3.33–3.46] | identical |
| sieve | 682 (676–690) | 275 (271–282) | 156 (147–169) | **4.36x** [4.05–4.63] | **1.76x** [1.63–1.87] | identical |
| spectral-norm | 632 (631–634) | 883 (875–898) | 620 (618–625) | **1.02x** [1.01–1.02] | **1.42x** [1.41–1.44] | identical |

**Whole process.** 4 iterations plus startup, median per process,
node / bun / go:

| benchmark | cold 1st iteration | wall | CPU (user+sys) | peak RSS |
| --- | ---: | ---: | ---: | ---: |
| array-hof | 838 / 253 / 28.9 ms | 3228 / 812 / 150 ms | 3207 / 754 / 129 ms | 133 / 58 / 10 MB |
| bytecode-vm | 1010 / 300 / 319 ms | 4060 / 1289 / 1275 ms | 4013 / 1295 / 1268 ms | 51 / 41 / 10 MB |
| collatz | 1655 / 3724 / 1145 ms | 7129 / 15899 / 4547 ms | 7078 / 15885 / 4556 ms | 51 / 40 / 10 MB |
| dijkstra | 367 / 352 / 363 ms | 1594 / 1688 / 1634 ms | 1653 / 1795 / 1765 ms | 188 / 145 / 79 MB |
| fib | 410 / 298 / 225 ms | 1678 / 1214 / 910 ms | 1672 / 1209 / 904 ms | 51 / 37 / 10 MB |
| fuzzy-search | 714 / 434 / 429 ms | 2886 / 1751 / 1732 ms | 2923 / 1802 / 1730 ms | 63 / 53 / 10 MB |
| game-of-life | 1118 / 1090 / 576 ms | 4428 / 4308 / 2267 ms | 4458 / 4336 / 2300 ms | 185 / 118 / 12 MB |
| log-analytics | 698 / 618 / 256 ms | 2377 / 2323 / 881 ms | 4456 / 2958 / 1075 ms | 531 / 592 / 145 MB |
| mandelbrot | 1148 / 1172 / 1134 ms | 4636 / 4691 / 4526 ms | 4621 / 4679 / 4524 ms | 53 / 39 / 10 MB |
| nbody | 417 / 579 / 470 ms | 1713 / 2318 / 1895 ms | 1712 / 2320 / 1890 ms | 53 / 41 / 10 MB |
| orders | 496 / 747 / 217 ms | 1772 / 2912 / 672 ms | 2594 / 3209 / 954 ms | 541 / 297 / 176 MB |
| particles | 332 / 518 / 33.8 ms | 1204 / 2074 / 136 ms | 1223 / 3870 / 137 ms | 85 / 47 / 10 MB |
| raytracer | 451 / 534 / 131 ms | 1591 / 1898 / 527 ms | 1652 / 2467 / 528 ms | 57 / 53 / 10 MB |
| sieve | 717 / 377 / 180 ms | 2819 / 1241 / 670 ms | 3005 / 1295 / 742 ms | 188 / 187 / 12 MB |
| spectral-norm | 680 / 894 / 622 ms | 2633 / 3599 / 2495 ms | 2651 / 3617 / 2497 ms | 55 / 43 / 10 MB |

`orders` and `raytracer` come from a second run of the same harness,
made after the struct-size limit described below, and `bytecode-vm`
from a third, after its `switch` became a jump table.

## What the numbers say

- **Memory is the most consistent win.** The Go binary's peak RSS is
  lower in every benchmark. It is about 10 MB where the JS engines sit
  at 40–60 MB, and 12 MB vs 188 MB (Node) for `sieve`, whose
  `boolean[]` becomes a 1-byte-per-element `[]bool`.
- **Allocation-heavy code now wins the most.** Two changes remove the
  allocations that V8's and JavaScriptCore's young-generation GCs
  absorb and Go's collector doesn't:
  - `array-hof` fuses its `map`/`filter`/`reduce` chains into one loop.
  - `particles` stores its small `{x, y}` vectors as Go values instead
    of heap objects.
- **Record- and object-heavy code** (`orders`, `raytracer`) is 2.6–4.9x
  faster than both. Static types remove what both JITs have to discover
  and guard at runtime.
- **Integer-heavy code gains from `Int`.** `game-of-life`,
  `log-analytics` and `sieve` do index arithmetic, which is now Go
  `int` arithmetic (see [Integers](#integers-int-as-a-go-int)).
- **Ties and losses:**
  - **Tight float loops** (`mandelbrot`, `spectral-norm`) tie with
    Node: once warm, a JIT emits the same machine code Go does.
  - **`nbody`** is 12% slower than Node, and **`dijkstra`** 8%; see
    [Where Go still loses](#where-go-still-loses).
  - **`bytecode-vm`** ties with Bun. Its remaining cost is `%` on a
    `Number[]` stack (the program's own annotation), which Go computes
    on doubles. JavaScriptCore most likely keeps these whole-number
    values as 32-bit integers (as V8 does with its Smis), but that
    isn't measured here.

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
these changes). The [Integers](#integers-int-as-a-go-int) section has
the `Int` change's share on its own.

## Where Go still loses

Profiles and hand-edited variants of the generated Go attribute each
remaining loss to its cause.

**`dijkstra` (8% behind Node)** is memory-bound: the hot lines are
loads from the graph's arrays and the heap. Two causes, measured by
editing the generated Go:

| variant | warm |
| --- | ---: |
| as generated | 355 ms |
| heap index math unchecked (`2*i`, `(i-1)/2`) | 345 ms |
| … and 4-byte (`int32`) graph arrays | **321 ms** |
| Node | 318–322 ms |

- **Checked arithmetic:** the checked multiply (`intyIMul`) and the
  float floor on heap indices guard against values past 2^53. Here they
  can't be past it, since they index an array.
- **Array width:** Go's `[]int` takes 8 bytes per element. `int32`
  halves the cache traffic of the graph arrays. This is a way for Go to
  catch up, not what Node does: Node's arrays of small integers also
  take 8 bytes per element (measured: official Node builds don't
  enable V8's pointer compression, which would make them 4). The rest
  of Node's lead isn't attributed yet.

Both fixes need a range analysis that proves the values fit.

**`nbody` (12% behind Node)** is limited by `sqrt` and division latency,
which V8 pays too. The difference is `bi.vx/vy/vz`, three running sums
that go through memory on every inner iteration:

| variant | warm |
| --- | ---: |
| as generated | 467 ms |
| slice header and masses hoisted into locals | 466 ms |
| `bi`'s fields kept in locals across the inner loop | **302 ms** |
| Node | 408–470 ms |

Go can't keep them in registers, because `bj` might be the same object
as `bi`. inty can't do it either without changing meaning: the types
don't rule out an array holding one object twice.

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
`y * W + x` a call and the program 76% *slower*.

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

