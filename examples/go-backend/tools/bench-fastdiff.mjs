#!/usr/bin/env node
// End-to-end benchmark of the fastdiff CLI (a port of npm fast-diff): the
// translated Go binary vs the same JavaScript under Node and (when
// installed) Bun, as whole processes — startup, reading both files,
// diffing, printing the diff.
//
// Inputs (all ASCII, generated deterministically from the repository's
// own sources with a seeded PRNG):
// - small: the repository README vs a copy with a handful of edits;
// - large: the first 2 MB of the repository's Rust sources concatenated,
//   vs a copy with 40 scattered insertions, deletions, replacements and
//   moved blocks (with and without --cleanup);
// - dense: 100 KB of the same with 2000 small edits (one every ~50
//   characters), so the half-match speedup rarely applies and the Myers
//   bisection does most of the work.
//
// Every side must print byte-identical output. Runs are interleaved in
// random order across `--runs` rounds (after one discarded warm-up
// round) so drift affects every side equally; wall time, CPU time
// (user + sys) and peak RSS come from getrusage(RUSAGE_CHILDREN) in a
// small Python wrapper, as in bench.mjs.
//
// Usage: node bench-fastdiff.mjs [--runs N] [--inty path] [--no-bun] [--only id,id]
//
// Bun runs with whatever BUN_OPTIONS the environment sets (the numbers in
// BENCHMARKS.md use none; `--smol` trades Bun's speed for memory).

import { spawnSync } from "node:child_process";
import { mkdtempSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const repo = resolve(here, "../../..");
const tool = join(here, "fastdiff.js");

const argv = process.argv.slice(2);
let runs = 21;
let inty = null;
let noBun = false;
let only = null;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === "--runs") runs = Number(argv[++i]);
  else if (argv[i] === "--inty") inty = resolve(argv[++i]);
  else if (argv[i] === "--no-bun") noBun = true;
  else if (argv[i] === "--only") only = argv[++i].split(",");
}

function must(cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { encoding: "utf8", maxBuffer: 1 << 30, ...opts });
  if (r.error) throw r.error;
  if (r.status !== 0) throw new Error(`${cmd} ${args.join(" ")} failed:\n${r.stdout}${r.stderr}`);
  return r;
}

const MEASURE_PY = `
import json, resource, subprocess, sys, time
t0 = time.perf_counter()
p = subprocess.run(sys.argv[1:], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
t1 = time.perf_counter()
u = resource.getrusage(resource.RUSAGE_CHILDREN)
print(json.dumps({"code": p.returncode, "wall": (t1 - t0) * 1e3,
                  "cpu": (u.ru_utime + u.ru_stime) * 1e3, "rssKb": u.ru_maxrss}))
`;
function sample(cmd, args) {
  const r = JSON.parse(must("python3", ["-c", MEASURE_PY, cmd, ...args]).stdout);
  if (r.code !== 0) throw new Error(`${cmd} exited ${r.code}`);
  return r;
}

// ---- inputs --------------------------------------------------------------

let seed = 20240917;
const rand = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
const randInt = (n) => Math.floor(rand() * n);
const ascii = (s) => s.replace(/[^\x00-\x7f]/g, "?");
const WORDS = ["let", "value", "result", "index", " ", "\n", "(", ")", ";", "x", "self", "fn", "=", "0", "if", "{", "}"];
const randText = (n) => {
  let s = "";
  while (s.length < n) s += WORDS[randInt(WORDS.length)];
  return s.slice(0, n);
};

// `edits` random edits of `text`: insertions, deletions and replacements
// of up to `maxLen` characters, and (if `move`) moved blocks of up to
// 20 * maxLen characters.
function edit(text, edits, maxLen, move) {
  let t = text;
  for (let e = 0; e < edits; e++) {
    const at = randInt(t.length);
    const len = 1 + randInt(maxLen);
    switch (randInt(move ? 4 : 3)) {
      case 0:
        t = t.slice(0, at) + randText(len) + t.slice(at);
        break;
      case 1:
        t = t.slice(0, at) + t.slice(at + len);
        break;
      case 2:
        t = t.slice(0, at) + randText(len) + t.slice(at + len);
        break;
      default: {
        const block = t.slice(at, at + len * 20);
        t = t.slice(0, at) + t.slice(at + block.length);
        const to = randInt(t.length);
        t = t.slice(0, to) + block + t.slice(to);
      }
    }
  }
  return t;
}

function files(dir, ext) {
  const out = [];
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    if (e.name.startsWith(".") || e.name === "target" || e.name === "node_modules") continue;
    const p = join(dir, e.name);
    if (e.isDirectory()) out.push(...files(p, ext));
    else if (e.name.endsWith(ext)) out.push(p);
  }
  return out.sort();
}

const work = mkdtempSync(join(tmpdir(), "fastdiff-bench-"));
function pair(id, a, b, flags = []) {
  const fa = join(work, `${id}.a.txt`);
  const fb = join(work, `${id}.b.txt`);
  writeFileSync(fa, a);
  writeFileSync(fb, b);
  return { id, args: [fa, fb, ...flags], bytes: statSync(fa).size + statSync(fb).size };
}
const readme = ascii(readFileSync(join(repo, "README.md"), "utf8"));
const rust = ascii(files(join(repo, "crates"), ".rs").map((f) => readFileSync(f, "utf8")).join("\n"));
const large = rust.slice(0, 2 << 20);
const largeEdited = edit(large, 40, 20, true);
const dense = rust.slice(0, 100 << 10);
let inputs = [
  pair("small", readme, edit(readme, 6, 20, true)),
  pair("large", large, largeEdited),
  pair("large-cleanup", large, largeEdited, ["--cleanup"]),
  pair("dense", dense, edit(dense, 2000, 4, false)),
];
if (only) inputs = inputs.filter((x) => only.includes(x.id));

// ---- sides ---------------------------------------------------------------

if (!inty) {
  must("cargo", ["build", "--release", "-p", "inty-cli"], { cwd: repo, stdio: "inherit" });
  inty = join(repo, "target/release/inty");
}
must(inty, ["go", "--no-color", tool, "-o", join(work, "main.go")]);
writeFileSync(join(work, "go.mod"), "module fastdiff\n\ngo 1.22\n");
must("go", ["build", "-o", "fastdiff", "."], { cwd: work });
const sides = [
  { id: "node", cmd: "node", pre: [tool], version: `node ${process.version}` },
];
const bun = noBun ? null : spawnSync("bun", ["--version"], { encoding: "utf8" });
if (bun && bun.status === 0) {
  sides.push({ id: "bun", cmd: "bun", pre: [tool], version: `bun ${bun.stdout.trim()}` });
}
sides.push({ id: "go", cmd: join(work, "fastdiff"), pre: [], version: must("go", ["version"]).stdout.trim() });

// Same output everywhere.
for (const input of inputs) {
  const outs = sides.map((s) => must(s.cmd, [...s.pre, ...input.args]).stdout);
  for (let i = 1; i < outs.length; i++) {
    if (outs[i] !== outs[0]) throw new Error(`${sides[i].id} output differs on ${input.id}`);
  }
  input.summary = outs[0].slice(0, outs[0].indexOf("\n"));
}

// ---- measure -------------------------------------------------------------

let order = 7;
const shuffleRand = () => ((order = (order * 1103515245 + 12345) % 2147483648) / 2147483648);
const data = {};
for (const input of inputs) for (const s of sides) data[`${input.id}/${s.id}`] = [];
for (let round = 0; round <= runs; round++) {
  const jobs = inputs.flatMap((input) => sides.map((s) => [input, s]));
  for (let i = jobs.length - 1; i > 0; i--) {
    const j = Math.floor(shuffleRand() * (i + 1));
    [jobs[i], jobs[j]] = [jobs[j], jobs[i]];
  }
  for (const [input, s] of jobs) {
    const r = sample(s.cmd, [...s.pre, ...input.args]);
    if (round > 0) data[`${input.id}/${s.id}`].push(r);
  }
}

const median = (xs) => {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
};
const fmt = (x) => (x >= 100 ? x.toFixed(0) : x.toFixed(1));
console.log(`\n${sides.map((s) => s.version).join(", ")}; ${runs} interleaved runs per cell, median.\n`);
for (const input of inputs) console.log(`${input.id}: ${input.summary}`);
console.log();
console.log(`| input | ${sides.map((s) => `${s.id} wall`).join(" | ")} | ${sides.map((s) => `${s.id} CPU`).join(" | ")} | ${sides.map((s) => `${s.id} RSS`).join(" | ")} | go speedup vs ${sides.filter((s) => s.id !== "go").map((s) => s.id).join(" / ")} |`);
console.log(`| --- |${" ---: |".repeat(sides.length * 3 + 1)}`);
for (const input of inputs) {
  const m = (s, k) => median(data[`${input.id}/${s.id}`].map((r) => r[k]));
  const go = sides.find((s) => s.id === "go");
  const size = input.bytes >= 1 << 20 ? `${(input.bytes / (1 << 20)).toFixed(1)} MB` : `${(input.bytes / 1024).toFixed(1)} KB`;
  console.log(
    `| ${input.id} (${size}) | ${sides.map((s) => `${fmt(m(s, "wall"))} ms`).join(" | ")} | ` +
      `${sides.map((s) => `${fmt(m(s, "cpu"))} ms`).join(" | ")} | ` +
      `${sides.map((s) => `${(m(s, "rssKb") / 1024).toFixed(0)} MB`).join(" | ")} | ` +
      `${sides.filter((s) => s.id !== "go").map((s) => `${(m(s, "wall") / m(go, "wall")).toFixed(2)}x`).join(" / ")} |`,
  );
}
