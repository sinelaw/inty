# Benchmarks: inty → Go vs Node and Bun

This compares the Go translation produced by `inty go` with the original,
unmodified JavaScript running under **Node (V8)** and **Bun
(JavaScriptCore)**. The programs and the harness are in this directory;
see the [README](README.md) for what the backend supports.

**Summary.**
- **Memory:** the Go binary uses the least memory in all 15 benchmarks,
  typically ~10 MB against 40–60 MB, and up to 19x less than Node.
- **Speed vs both engines:** it beats Node and Bun by 2–3x on the record-
  and object-heavy workloads (`orders`, `raytracer`), and by 1.4–4x on
  call-heavy and dense-array code (`fib`, `sieve`).
- **Speed vs Node alone:** it is also 1.3–2.8x faster than Node on
  closure pipelines, a bytecode interpreter and a string DP, where Bun
  beats it by 1.2–1.8x.
- **Ties and losses:** pure float loops are a tie. Short-lived allocation
  (vs V8) and integer index arithmetic done in doubles are losses.
- **Integers:** since inty types integers as `Int` and the backend emits
  them as Go `int`, every program is 0–42% faster than the float64 code
  the tables below measured. See [Integers](#integers-int-as-a-go-int).

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
1.24.7 on a 4-core linux/amd64 cloud container. They predate the `Int`
lowering: [Integers](#integers-int-as-a-go-int) has its before/after. Each runtime got 10
processes after 1 discarded, so 30 warm iterations. Every program's
output was byte-identical across all three. On their own, the runtimes
take 28 ms (Node) and 3.8 ms (Bun) to start.

**Steady state.** Warm iterations only, so JIT warm-up and startup are
excluded. Median ms (IQR). Speedup = JS time / Go time, with a 95% CI:

| benchmark | node warm | bun warm | inty → go warm | **vs node** [95% CI] | **vs bun** [95% CI] | output |
| --- | ---: | ---: | ---: | ---: | ---: | :---: |
| array-hof | 836 (781–859) | 171 (161–183) | 298 (280–322) | **2.80x** [2.55–2.97] | **0.57x** [0.53–0.63] | identical |
| bytecode-vm | 924 (863–954) | 263 (234–280) | 452 (431–478) | **2.04x** [1.91–2.12] | **0.58x** [0.51–0.61] | identical |
| collatz | 1516 (1470–1559) | 3257 (3165–3335) | 1036 (1017–1084) | **1.46x** [1.39–1.49] | **3.14x** [3.02–3.21] | identical |
| dijkstra | 321 (296–330) | 346 (336–360) | 383 (348–394) | **0.84x** [0.77–0.91] | **0.90x** [0.88–0.98] | identical |
| fib | 358 (340–375) | 237 (216–249) | 171 (168–178) | **2.09x** [1.98–2.16] | **1.39x** [1.27–1.46] | identical |
| fuzzy-search | 628 (594–652) | 372 (348–385) | 466 (457–484) | **1.35x** [1.29–1.39] | **0.80x** [0.75–0.82] | identical |
| game-of-life | 932 (901–984) | 897 (870–930) | 883 (864–909) | **1.06x** [1.02–1.10] | **1.02x** [0.99–1.04] | identical |
| log-analytics | 577 (473–640) | 491 (468–546) | 454 (382–517) | **1.27x** [1.11–1.45] | **1.08x** [0.99–1.25] | identical |
| mandelbrot | 878 (842–906) | 896 (873–926) | 883 (849–912) | **1.00x** [0.97–1.03] | **1.02x** [0.99–1.05] | identical |
| nbody | 367 (348–387) | 501 (486–526) | 407 (388–424) | **0.90x** [0.86–0.94] | **1.23x** [1.20–1.27] | identical |
| orders | 396 (365–471) | 631 (601–668) | 203 (192–216) | **1.95x** [1.78–2.06] | **3.10x** [2.93–3.23] | identical |
| particles | 256 (239–272) | 606 (590–638) | 386 (374–402) | **0.66x** [0.62–0.69] | **1.57x** [1.50–1.66] | identical |
| raytracer | 384 (363–411) | 450 (428–476) | 185 (178–191) | **2.07x** [1.98–2.22] | **2.43x** [2.31–2.58] | identical |
| sieve | 780 (750–800) | 320 (305–340) | 196 (182–210) | **3.99x** [3.81–4.26] | **1.64x** [1.55–1.75] | identical |
| spectral-norm | 585 (559–604) | 773 (752–792) | 586 (576–605) | **1.00x** [0.96–1.02] | **1.32x** [1.27–1.35] | identical |

**Whole process.** 4 iterations plus startup, median per process,
node / bun / go:

| benchmark | cold 1st iteration | wall | CPU (user+sys) | peak RSS |
| --- | ---: | ---: | ---: | ---: |
| array-hof | 877 / 190 / 286 ms | 3427 / 741 / 1173 ms | 3420 / 951 / 1826 ms | 131 / 61 / 12 MB |
| bytecode-vm | 918 / 250 / 446 ms | 3682 / 1058 / 1801 ms | 3638 / 1055 / 1796 ms | 51 / 41 / 10 MB |
| collatz | 1399 / 2881 / 1030 ms | 5934 / 12669 / 4177 ms | 5843 / 12513 / 4145 ms | 51 / 40 / 10 MB |
| dijkstra | 357 / 355 / 392 ms | 1530 / 1635 / 1723 ms | 1570 / 1709 / 1818 ms | 192 / 145 / 96 MB |
| fib | 343 / 250 / 175 ms | 1460 / 958 / 675 ms | 1417 / 948 / 674 ms | 51 / 37 / 10 MB |
| fuzzy-search | 647 / 394 / 451 ms | 2529 / 1495 / 1847 ms | 2528 / 1518 / 1831 ms | 63 / 53 / 10 MB |
| game-of-life | 931 / 948 / 871 ms | 3754 / 3664 / 3502 ms | 3725 / 3661 / 3483 ms | 186 / 109 / 10 MB |
| log-analytics | 699 / 563 / 526 ms | 2467 / 2113 / 1959 ms | 4734 / 2821 / 2926 ms | 534 / 514 / 201 MB |
| mandelbrot | 903 / 930 / 858 ms | 3553 / 3603 / 3527 ms | 3485 / 3570 / 3477 ms | 53 / 39 / 10 MB |
| nbody | 371 / 505 / 400 ms | 1529 / 2022 / 1621 ms | 1513 / 2010 / 1598 ms | 53 / 41 / 10 MB |
| orders | 504 / 672 / 249 ms | 1857 / 2589 / 878 ms | 2687 / 2841 / 1097 ms | 561 / 359 / 178 MB |
| particles | 324 / 610 / 388 ms | 1128 / 2434 / 1545 ms | 1131 / 4455 / 1723 ms | 85 / 46 / 10 MB |
| raytracer | 453 / 559 / 187 ms | 1653 / 1932 / 744 ms | 1688 / 2528 / 775 ms | 57 / 52 / 10 MB |
| sieve | 838 / 440 / 198 ms | 3240 / 1447 / 786 ms | 3415 / 1511 / 1128 ms | 210 / 186 / 11 MB |
| spectral-norm | 642 / 778 / 609 ms | 2436 / 3119 / 2394 ms | 2415 / 3109 / 2369 ms | 55 / 43 / 10 MB |

## What the numbers say

- **Memory is the most consistent win.** The Go binary's peak RSS is
  lower in every benchmark:
  - about 10 MB where the JS engines sit at 40–60 MB;
  - 11 MB vs 210 MB (Node) for `sieve`, whose `boolean[]` becomes a
    1-byte-per-element `[]bool`;
  - 178 MB vs 561 MB (Node) and 359 MB (Bun) for `orders`, whose million
    records become flat structs instead of objects with boxed
    double-valued fields.
- **Record- and object-heavy code wins against both engines.** The Go
  binary is 2–3x faster on `orders` (the ETL pipeline) and `raytracer`
  (vector math on small objects). There, static types remove what both
  JITs have to discover and guard at runtime.
- **Call-heavy and dense-array code** (`fib`, `sieve`) is 1.4–4x faster
  than both.
- **Bun (JavaScriptCore) is the stronger baseline** on
  closure-heavy array pipelines (`array-hof`), the switch-dispatch
  interpreter (`bytecode-vm`) and the Levenshtein DP (`fuzzy-search`).
  There it beats the Go translation by 1.2–1.8x. It is weak on double
  `%` (`collatz`) and short-lived allocation (`particles`). Against Node,
  the Go translation wins or ties on all of these except `particles`.
- **Ties and losses are real too.** Tight float loops (`mandelbrot`,
  `spectral-norm`, `nbody`) are within about 10% of the best JIT: once
  warm, a JIT emits the same machine code Go does. V8's escape analysis
  and young-generation GC win on short-lived small objects (`particles`).
  Graph code with integer index arithmetic done in doubles (`dijkstra`)
  is slower in Go.

Where the Go backend loses, it's to things a better backend could fix;
the types already carry the information:
- **Integers as integers.** Every JS number is a `float64` here. Both
  JITs speculate on small integers, so index arithmetic and `switch`
  dispatch (which Go compiles to float comparison chains) are cheaper
  for them. A range analysis that proves values integral would let
  those become Go `int`s.
- **Fused array pipelines.** `map` / `filter` / `reduce` go through
  generic helpers that take a func value, so the callback isn't
  inlined. Emitting the loop at the call site when the callback is a
  literal would remove the indirect call.

## A real tool: md2html

[`tools/md2html.js`](tools/md2html.js) is a ~700-line Markdown → HTML
converter (CommonMark core plus GitHub tables and strikethrough) written
as ordinary JavaScript and reading and writing files through
`node:fs` / `node:process`. Unlike the programs above it isn't a loop
kernel with an in-process benchmark protocol: it's measured the way a
CLI is used, as **whole processes** — startup, reading the input,
converting, writing the HTML.

`node tools/bench.mjs` translates and builds it, checks that Node, Bun
and the Go binary produce byte-identical HTML, then runs each side 21
times per input (after one discarded warm-up round), interleaved in
random order. Wall time, CPU time (user + sys) and peak RSS come from
`getrusage`; medians are reported.

Inputs: the repository README (5.2 KB), and every Markdown file in the
repository concatenated and repeated to 20.4 MB.

| input | node | bun | inty → go | go vs node / bun | CPU node / bun / go | peak RSS node / bun / go |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small (5.2 KB) | 72.2 ms | 37.2 ms | 3.0 ms | **23.8x / 12.3x** | 75 / 43 / 4 ms | 58 / 44 / 10 MB |
| large (20.4 MB) | 1303 ms | 1129 ms | 821 ms | **1.59x / 1.37x** | 1734 / 2115 / 1126 ms | 332 / 459 / 149 MB |

Node v22.22.2, Bun 1.3.11, Go 1.24.7, linux/amd64.

- **Small inputs are startup.** A native binary starts in ~3 ms; the JS
  engines spend 35–70 ms before running a line. For a tool invoked once
  per file — a build step, a pre-commit hook — this is the number that
  matters.
- **Large inputs are throughput.** Here the gap is 1.4–1.6x in wall time,
  with 35–50% less CPU (the engines' JIT and GC threads work in parallel
  with the program) and less than half the memory.
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
| small (2 × 5 KB) | 111 ms | 71.8 ms | 14.9 ms | **7.4x / 4.8x** | 147 / 86 / 16 ms | 59 / 46 / 10 MB |
| large (2 × 2 MB) | 1753 ms | 2343 ms | 1921 ms | 0.91x / 1.22x | 1876 / 2418 / 2922 ms | 477 / 308 / 197 MB |
| large, `--cleanup` | 1728 ms | 2341 ms | 1916 ms | 0.90x / 1.22x | 1875 / 2415 / 2858 ms | 480 / 310 / 197 MB |
| dense (2 × 100 KB) | 626 ms | 1205 ms | 479 ms | **1.31x / 2.51x** | 762 / 1256 / 544 ms | 93 / 89 / 13 MB |

Node v22.22.2, Bun 1.3.11 (default options, i.e. without `--smol`),
Go 1.24.7, linux/amd64.

- **Small inputs:** the native binary wins by 5–7x. The gap is smaller
  than for md2html because even a 5 KB diff runs a few bisections.
- **Large input: Node wins by about 10%, and uses more than twice the
  memory.** Each bisection builds two arrays the size of both texts,
  about 4M elements at the top level and 21M pushes per array over the
  whole run. They are built with `push(-1)`, as upstream does with
  `new Array(n)` plus a fill loop. That makes this input a test of
  allocating and page-faulting large arrays. V8 stores them as 4-byte
  small integers; Go stores 8-byte `float64`s and returns freed pages to
  the OS, then faults them in again. Go's CPU time exceeds its wall time
  because of its concurrent GC. `GOGC=200` brings Go to about 1.45 s,
  but the benchmark uses defaults.
- **Dense input:** Myers bisection is character comparisons and index
  arithmetic on the V arrays, and Go wins: 1.3x vs Node and 2.5x vs
  Bun, at a seventh of the memory.
- **The runtime change this benchmark prompted:** `arr.push` now grows
  a full array to twice its length. Go's `append` grows large slices by
  only 1.25x, which copied the V arrays about five times over. That
  change took the large input from about 2.5 s (a single run) to 1.92 s. It is neutral or
  better on the other programs; `sieve` is ~20% faster as a whole
  process.
- **Where the types could still help:** the bisection indices are
  integral, so a range analysis could make the V arrays `[]int32`,
  halving the memory traffic that decides the large case.

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

