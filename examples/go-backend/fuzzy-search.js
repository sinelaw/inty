// Fuzzy search / spell-check suggestions: for each query, rank a
// 20k-word dictionary by Levenshtein distance (two-row dynamic
// programming over character codes) and report the best matches.
let seed = 99;
function rand() {
  seed = (seed * 16807) % 2147483647;
  return seed / 2147483647;
}

function randomWord() {
  const LETTERS = "etaoinshrdlcumwfgypbvkjxqz";
  const len = 4 + Math.floor(rand() * 8);
  let w = "";
  for (let i = 0; i < len; i++) {
    // Skewed towards common letters, like real text.
    const r = rand();
    w += LETTERS[Math.floor(r * r * LETTERS.length)];
  }
  return w;
}

/** function levenshtein(String, String, Number[], Number[]) => Number */
function levenshtein(a, b, prev, cur) {
  const n = a.length;
  const m = b.length;
  for (let j = 0; j <= m; j++) {
    prev[j] = j;
  }
  for (let i = 1; i <= n; i++) {
    cur[0] = i;
    const ca = a.charCodeAt(i - 1);
    for (let j = 1; j <= m; j++) {
      const cost = ca === b.charCodeAt(j - 1) ? 0 : 1;
      const del = prev[j] + 1;
      const ins = cur[j - 1] + 1;
      const sub = prev[j - 1] + cost;
      cur[j] = Math.min(Math.min(del, ins), sub);
    }
    for (let j = 0; j <= m; j++) {
      prev[j] = cur[j];
    }
  }
  return prev[m];
}

function main() {
  seed = 99;
  const lines = [];
  const dictionary = [];
  for (let i = 0; i < 20000; i++) {
    dictionary.push(randomWord());
  }
  const queries = [];
  for (let i = 0; i < 60; i++) {
    queries.push(randomWord());
  }

  const prev = [];
  const cur = [];
  for (let i = 0; i < 64; i++) {
    prev.push(0);
    cur.push(0);
  }

  let checksum = 0;
  for (const q of queries) {
    let best = 1000;
    let bestWord = "";
    let within2 = 0;
    for (const w of dictionary) {
      const d = levenshtein(q, w, prev, cur);
      if (d < best) {
        best = d;
        bestWord = w;
      }
      if (d <= 2) {
        within2++;
      }
    }
    checksum += best * 1000 + within2;
    if (queries.indexOf(q) < 5) {
      lines.push(`${q}: best "${bestWord}" (distance ${best}), ${within2} within 2`);
    }
  }
  lines.push(`checksum ${checksum}`);
  return lines.join("\n");
}

// ---- benchmark protocol (see bench.mjs) ------------------------------
// Run the workload 4 times in one process. The first run includes JIT
// warm-up; bench.mjs reports the other three as steady-state samples.
let report = "";
for (let iteration = 0; iteration < 4; iteration++) {
  const t0 = performance.now();
  report = main();
  console.error(`inty-bench iteration ${iteration} ms ${performance.now() - t0}`);
}
console.log(report);
