#!/usr/bin/env node
// Benchmark harness for the inty Go backend proof of concept.
//
// For every benchmark program in this directory:
//   1. `inty go prog.js -o <tmp>/prog/main.go`  (type-check + translate)
//   2. `go build`                               (native binary)
//   3. run the binary and `node prog.js`, check stdout is identical
//   4. time both (wall clock, median of N runs)
//
// Usage:
//   node bench.mjs [--runs N] [--inty path/to/inty] [name ...]
//
// Requires `go` and `node` on PATH. Builds inty with cargo unless
// `--inty` is given.

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const repo = resolve(here, "../..");

const args = process.argv.slice(2);
let runs = 5;
let inty = null;
const only = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--runs") runs = Number(args[++i]);
  else if (args[i] === "--inty") inty = resolve(args[++i]);
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
    process.stderr.write(r.stdout + r.stderr);
    throw new Error(`${cmd} ${argv.join(" ")} failed with status ${r.status}`);
  }
  return r;
}

function timeMs(cmd, argv) {
  const t0 = process.hrtime.bigint();
  const r = run(cmd, argv);
  const t1 = process.hrtime.bigint();
  if (r.status !== 0) throw new Error(`${cmd} ${argv.join(" ")} exited ${r.status}`);
  return Number(t1 - t0) / 1e6;
}

function median(xs) {
  const s = [...xs].sort((a, b) => a - b);
  return s[Math.floor(s.length / 2)];
}

if (!inty) {
  console.error("building inty (cargo build --release -p inty-cli)...");
  must("cargo", ["build", "--release", "-p", "inty-cli"], { cwd: repo, stdio: "inherit" });
  inty = join(repo, "target/release/inty");
}

const goVersion = must("go", ["version"]).stdout.trim();
const nodeVersion = process.version;
const work = mkdtempSync(join(tmpdir(), "inty-go-bench-"));

const programs = readdirSync(here)
  .filter((f) => f.endsWith(".js"))
  .map((f) => basename(f, ".js"))
  .filter((n) => only.length === 0 || only.includes(n))
  .sort();

const nodeStartup = median(Array.from({ length: runs }, () => timeMs("node", ["-e", ""])));

const rows = [];
for (const name of programs) {
  const src = join(here, `${name}.js`);
  const dir = join(work, name);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, "go.mod"), `module ${name.replace(/-/g, "_")}\n\ngo 1.22\n`);

  console.error(`[${name}] translating + building...`);
  must(inty, ["go", "--no-color", src, "-o", join(dir, "main.go")]);
  must("go", ["build", "-o", "prog", "."], { cwd: dir });
  const bin = join(dir, "prog");

  const nodeOut = must("node", [src]).stdout;
  const goOut = must(bin, []).stdout;
  const same = nodeOut === goOut;
  if (!same) {
    console.error(`[${name}] OUTPUT MISMATCH\n--- node\n${nodeOut}--- go\n${goOut}`);
  }

  console.error(`[${name}] timing (${runs} runs each)...`);
  const nodeMs = median(Array.from({ length: runs }, () => timeMs("node", [src])));
  const goMs = median(Array.from({ length: runs }, () => timeMs(bin, [])));
  rows.push({ name, nodeMs, goMs, same });
}

const fmt = (ms) => `${ms.toFixed(0)} ms`;
console.log(`\n${nodeVersion} (V8) vs ${goVersion}; median of ${runs} runs, wall clock`);
console.log(`node startup alone (node -e ""): ${fmt(nodeStartup)}\n`);
console.log("| benchmark | node | inty → go | speedup | output identical |");
console.log("| --- | ---: | ---: | ---: | :---: |");
for (const r of rows) {
  console.log(
    `| ${r.name} | ${fmt(r.nodeMs)} | ${fmt(r.goMs)} | ${(r.nodeMs / r.goMs).toFixed(2)}x | ${r.same ? "yes" : "**NO**"} |`,
  );
}
if (rows.some((r) => !r.same)) process.exitCode = 1;
