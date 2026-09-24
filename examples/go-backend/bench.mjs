#!/usr/bin/env node
// Benchmark harness for the inty Go backend proof of concept: the
// translated Go binary vs the original JavaScript under Node (V8) and,
// when installed, Bun (JavaScriptCore).
//
// For every benchmark program in this directory:
//   1. `inty go prog.js -o <tmp>/prog/main.go`  (type-check + translate)
//   2. `go build`                               (native binary)
//   3. run the binary, `node prog.js` and `bun prog.js` once and require
//      identical stdout
//   4. launch `--processes` fresh processes per side (after `--warmup`
//      discarded ones), INTERLEAVED in a random order within every round
//      so slow drift (CPU frequency, noisy neighbours, page cache) hits
//      every side equally instead of biasing whichever ran last
//
// Inside each process the program runs its workload 4 times (see the
// "benchmark protocol" footer of each .js file) and prints the time of
// every iteration, measured with performance.now(), to stderr. Iteration
// 0 is *cold*: for Node it includes JIT warm-up. Iterations 1-3 are
// *warm* (steady state). The headline is the warm speedup, so neither
// process startup nor JIT warm-up count against V8.
//
// Each process also records end-to-end wall-clock time, CPU time (user +
// sys, including GC and compiler threads) and peak RSS, via a small
// Python wrapper around getrusage(RUSAGE_CHILDREN).
//
// Reported per benchmark: medians with interquartile ranges, and the warm
// speedup (median node / median go) with a 95% confidence interval from
// a cluster bootstrap (whole processes are resampled, because iterations
// within one process are correlated).
//
// Usage:
//   node bench.mjs [--processes N] [--warmup W] [--inty path] [--json out.json]
//                  [--no-bun] [name ...]

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const repo = resolve(here, "../..");

const args = process.argv.slice(2);
let processes = 10;
let warmup = 1;
let inty = null;
let jsonOut = null;
let noBun = false;
const only = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--processes") processes = Number(args[++i]);
  else if (args[i] === "--warmup") warmup = Number(args[++i]);
  else if (args[i] === "--inty") inty = resolve(args[++i]);
  else if (args[i] === "--json") jsonOut = resolve(args[++i]);
  else if (args[i] === "--no-bun") noBun = true;
  else only.push(args[i].replace(/\.js$/, ""));
}

function run(cmd, argv, opts = {}) {
  const r = spawnSync(cmd, argv, { encoding: "utf8", maxBuffer: 1 << 28, ...opts });
  if (r.error) throw r.error;
  return r;
}

function must(cmd, argv, opts) {
  const r = run(cmd, argv, opts);
  if (r.status !== 0) {
    process.stderr.write((r.stdout || "") + (r.stderr || ""));
    throw new Error(`${cmd} ${argv.join(" ")} failed with status ${r.status}`);
  }
  return r;
}

// Runs argv as a child of python and reports its wall time, CPU time,
// peak RSS and stderr. Python's own startup is outside the timed region.
const MEASURE_PY = `
import json, resource, subprocess, sys, time
t0 = time.perf_counter()
p = subprocess.run(sys.argv[1:], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
t1 = time.perf_counter()
u = resource.getrusage(resource.RUSAGE_CHILDREN)
print(json.dumps({"code": p.returncode, "wall": (t1 - t0) * 1e3,
                  "cpu": (u.ru_utime + u.ru_stime) * 1e3, "rssKb": u.ru_maxrss, "stderr": p.stderr}))
`;
must("python3", ["-c", "import resource"]);

function sample(cmd, argv) {
  const r = JSON.parse(must("python3", ["-c", MEASURE_PY, cmd, ...argv]).stdout);
  if (r.code !== 0) throw new Error(`${cmd} ${argv.join(" ")} exited ${r.code}:\n${r.stderr}`);
  const iters = [...r.stderr.matchAll(/^inty-bench iteration (\d+) ms ([\d.e+-]+)$/gm)].map((m) => Number(m[2]));
  if (iters.length < 2) throw new Error(`${cmd}: no benchmark-protocol timings on stderr`);
  return { wall: r.wall, cpu: r.cpu, rssMb: r.rssKb / 1024, cold: iters[0], warm: iters.slice(1) };
}

// ---- statistics ------------------------------------------------------------

function quantile(xs, q) {
  const s = [...xs].sort((a, b) => a - b);
  const pos = (s.length - 1) * q;
  const lo = Math.floor(pos);
  const hi = Math.ceil(pos);
  return s[lo] + (s[hi] - s[lo]) * (pos - lo);
}
const median = (xs) => quantile(xs, 0.5);

// Deterministic PRNG (mulberry32) so the bootstrap and run order are
// reproducible for a given set of samples.
function rng(seed) {
  return () => {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// 95% CI of median(a)/median(b), where a and b are lists of clusters
// (one array of samples per process); clusters are resampled whole.
function bootstrapRatioCI(a, b, iters = 5000) {
  const r = rng(12345);
  const resample = (cs) => cs.flatMap(() => cs[Math.floor(r() * cs.length)]);
  const ratios = [];
  for (let i = 0; i < iters; i++) ratios.push(median(resample(a)) / median(resample(b)));
  return [quantile(ratios, 0.025), quantile(ratios, 0.975)];
}

// ---- main --------------------------------------------------------------------

if (!inty) {
  console.error("building inty (cargo build --release -p inty-cli)...");
  must("cargo", ["build", "--release", "-p", "inty-cli"], { cwd: repo, stdio: "inherit" });
  inty = join(repo, "target/release/inty");
}

const goVersion = must("go", ["version"]).stdout.trim();
const work = mkdtempSync(join(tmpdir(), "inty-go-bench-"));
const order = rng(2024);

// JavaScript runtimes to compare against: Node (V8) always, Bun
// (JavaScriptCore) when it's on PATH and not disabled with --no-bun.
const runtimes = [{ id: "node", cmd: "node", version: `node ${process.version} (V8)` }];
const bun = noBun ? { status: 1 } : run("bun", ["--version"]);
if (bun.status === 0) runtimes.push({ id: "bun", cmd: "bun", version: `bun ${bun.stdout.trim()} (JavaScriptCore)` });
const sideIds = [...runtimes.map((r) => r.id), "go"];

function shuffled(xs) {
  const a = [...xs];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(order() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

const programs = readdirSync(here)
  .filter((f) => f.endsWith(".js"))
  .map((f) => basename(f, ".js"))
  .filter((n) => only.length === 0 || only.includes(n))
  .sort();

const results = [];
for (const name of programs) {
  const src = join(here, `${name}.js`);
  const dir = join(work, name);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, "go.mod"), `module ${name.replace(/-/g, "_")}\n\ngo 1.22\n`);

  console.error(`[${name}] translating + building...`);
  must(inty, ["go", "--no-color", src, "-o", join(dir, "main.go")]);
  must("go", ["build", "-o", "prog", "."], { cwd: dir });
  const bin = join(dir, "prog");

  const sides = { go: [bin, []] };
  for (const rt of runtimes) sides[rt.id] = [rt.cmd, [src]];

  // Every JS runtime and the Go binary must print the same thing.
  const outs = Object.fromEntries(sideIds.map((id) => [id, must(...sides[id]).stdout]));
  const same = sideIds.every((id) => outs[id] === outs.node);
  if (!same) {
    for (const id of sideIds) console.error(`[${name}] --- ${id}\n${outs[id]}`);
    console.error(`[${name}] OUTPUT MISMATCH`);
  }

  const data = Object.fromEntries(sideIds.map((id) => [id, []]));
  console.error(`[${name}] ${warmup} warm-up + ${processes} interleaved processes per side (${sideIds.join(", ")})...`);
  for (let round = 0; round < warmup + processes; round++) {
    for (const side of shuffled(sideIds)) {
      const s = sample(...sides[side]);
      if (round >= warmup) data[side].push(s);
    }
  }
  results.push({ name, same, data });
}

const startup = {};
for (const rt of runtimes) {
  startup[rt.id] = [];
  for (let i = 0; i < processes; i++) {
    const t0 = process.hrtime.bigint();
    must(rt.cmd, ["-e", ""]);
    startup[rt.id].push(Number(process.hrtime.bigint() - t0) / 1e6);
  }
}

const ms = (x) => (x >= 100 ? x.toFixed(0) : x.toFixed(1));
const spread = (xs) => `${ms(median(xs))} (${ms(quantile(xs, 0.25))}–${ms(quantile(xs, 0.75))})`;
const ratio = (a, b) => `${(median(a) / median(b)).toFixed(2)}x`;
const js = runtimes.map((r) => r.id);

console.log(`\n${runtimes.map((r) => r.version).join(" and ")} vs ${goVersion}`);
console.log(
  `${processes} processes per side (after ${warmup} discarded), interleaved in random order; ` +
    `${processes * 3} warm iterations per side. Startup alone (-e ""): ` +
    runtimes.map((r) => `${r.id} ${ms(median(startup[r.id]))} ms`).join(", ") +
    "\n",
);
console.log("Steady state (warm iterations, after in-process warm-up), median ms (IQR). Speedup = JS time / Go time:\n");
console.log(
  `| benchmark | ${js.map((id) => `${id} warm`).join(" | ")} | inty → go warm | ${js.map((id) => `**vs ${id}** [95% CI]`).join(" | ")} | output |`,
);
console.log(`| --- | ${sideIds.map(() => "---:").join(" | ")} | ${js.map(() => "---:").join(" | ")} | :---: |`);
for (const r of results) {
  const warm = (id) => r.data[id].map((s) => s.warm);
  const g = warm("go");
  const cells = js.map((id) => {
    const [lo, hi] = bootstrapRatioCI(warm(id), g);
    return `**${ratio(warm(id).flat(), g.flat())}** [${lo.toFixed(2)}–${hi.toFixed(2)}]`;
  });
  console.log(
    `| ${r.name} | ${sideIds.map((id) => spread(warm(id).flat())).join(" | ")} | ${cells.join(" | ")} | ${r.same ? "identical" : "**DIFFERS**"} |`,
  );
}
console.log(`\nWhole process (4 iterations + startup), median per process, ${sideIds.join(" / ")}:\n`);
console.log("| benchmark | cold 1st iteration | wall | CPU (user+sys) | peak RSS |");
console.log("| --- | ---: | ---: | ---: | ---: |");
for (const r of results) {
  const cell = (k, unit, f = ms) =>
    `${sideIds.map((id) => f(median(r.data[id].map((s) => s[k])))).join(" / ")} ${unit}`;
  console.log(
    `| ${r.name} | ${cell("cold", "ms")} | ${cell("wall", "ms")} | ${cell("cpu", "ms")} | ${cell("rssMb", "MB", (x) => x.toFixed(0))} |`,
  );
}

if (jsonOut) {
  writeFileSync(
    jsonOut,
    JSON.stringify({ runtimes, go: goVersion, processes, warmup, startup, results }, null, 1),
  );
  console.error(`raw samples written to ${jsonOut}`);
}
if (results.some((r) => !r.same)) process.exitCode = 1;
