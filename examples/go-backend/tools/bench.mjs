#!/usr/bin/env node
// End-to-end benchmark of the md2html CLI: the translated Go binary vs
// the same JavaScript under Node and (when installed) Bun, as whole
// processes — startup, reading the file, converting, writing the HTML.
//
// Two inputs: a small document (the repository README: startup
// dominates) and a large one (every Markdown file in the repository,
// repeated to ~20 MB: throughput dominates). Every side must produce
// byte-identical HTML. Runs are interleaved in random order across
// `--runs` rounds (after one discarded warm-up round) so drift affects
// every side equally; wall time, CPU time (user + sys) and peak RSS come
// from getrusage(RUSAGE_CHILDREN) in a small Python wrapper.
//
// Usage: node bench.mjs [--runs N] [--inty path] [--no-bun]

import { spawnSync } from "node:child_process";
import { mkdtempSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const repo = resolve(here, "../../..");
const tool = join(here, "md2html.js");

const argv = process.argv.slice(2);
let runs = 15;
let inty = null;
let noBun = false;
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === "--runs") runs = Number(argv[++i]);
  else if (argv[i] === "--inty") inty = resolve(argv[++i]);
  else if (argv[i] === "--no-bun") noBun = true;
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

function markdownFiles(dir) {
  const out = [];
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    if (e.name.startsWith(".") || e.name === "target" || e.name === "node_modules") continue;
    const p = join(dir, e.name);
    if (e.isDirectory()) out.push(...markdownFiles(p));
    else if (e.name.endsWith(".md")) out.push(p);
  }
  return out.sort();
}
const work = mkdtempSync(join(tmpdir(), "md2html-bench-"));
const small = join(repo, "README.md");
const corpus = markdownFiles(repo).map((f) => readFileSync(f, "utf8")).join("\n\n");
const large = join(work, "large.md");
writeFileSync(large, corpus.repeat(Math.ceil((20 << 20) / corpus.length)));
const inputs = [
  { id: "small", file: small, bytes: statSync(small).size },
  { id: "large", file: large, bytes: statSync(large).size },
];

// ---- sides ---------------------------------------------------------------

if (!inty) {
  must("cargo", ["build", "--release", "-p", "inty-cli"], { cwd: repo, stdio: "inherit" });
  inty = join(repo, "target/release/inty");
}
must(inty, ["go", "--no-color", tool, "-o", join(work, "main.go")]);
writeFileSync(join(work, "go.mod"), "module md2html\n\ngo 1.22\n");
must("go", ["build", "-o", "md2html", "."], { cwd: work });
const sides = [
  { id: "node", cmd: "node", pre: [tool], version: `node ${process.version}` },
];
const bun = noBun ? null : spawnSync("bun", ["--version"], { encoding: "utf8" });
if (bun && bun.status === 0) {
  sides.push({ id: "bun", cmd: "bun", pre: [tool], version: `bun ${bun.stdout.trim()}` });
}
sides.push({ id: "go", cmd: join(work, "md2html"), pre: [], version: must("go", ["version"]).stdout.trim() });

// Same HTML everywhere.
for (const input of inputs) {
  const outs = sides.map((s) => must(s.cmd, [...s.pre, input.file]).stdout);
  for (let i = 1; i < outs.length; i++) {
    if (outs[i] !== outs[0]) throw new Error(`${sides[i].id} output differs on ${input.id}`);
  }
}

// ---- measure -------------------------------------------------------------

let seed = 7;
const rand = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
const data = {};
for (const input of inputs) for (const s of sides) data[`${input.id}/${s.id}`] = [];
for (let round = 0; round <= runs; round++) {
  const jobs = inputs.flatMap((input) => sides.map((s) => [input, s]));
  for (let i = jobs.length - 1; i > 0; i--) {
    const j = Math.floor(rand() * (i + 1));
    [jobs[i], jobs[j]] = [jobs[j], jobs[i]];
  }
  for (const [input, s] of jobs) {
    const r = sample(s.cmd, [...s.pre, input.file, "-o", join(work, `${s.id}.html`)]);
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
