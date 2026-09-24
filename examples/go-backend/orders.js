// An ETL-style batch job: synthesise a day of e-commerce orders, then
// validate, enrich, aggregate per region and category, and pick the
// top customers. Millions of small records with numeric fields — the
// bread and butter of backend data processing.
let seed = 7;
function rand() {
  seed = (seed * 16807) % 2147483647;
  return seed / 2147483647;
}
function randInt(n) {
  return Math.floor(rand() * n);
}

const REGIONS = ["north", "south", "east", "west", "central"];
const CATEGORIES = ["books", "games", "garden", "kitchen", "music", "sports", "toys", "tools"];
const CUSTOMERS = 50000;

function makeOrder(id) {
  const qty = 1 + randInt(5);
  const price = Math.round(rand() * 20000) / 100;
  return {
    id: id,
    customer: randInt(CUSTOMERS),
    region: randInt(REGIONS.length),
    category: randInt(CATEGORIES.length),
    qty: qty,
    unitPrice: price,
    discount: rand() < 0.2 ? 0.1 : 0,
    refunded: rand() < 0.03,
  };
}

function lineTotal(o) {
  const gross = o.qty * o.unitPrice;
  return gross - gross * o.discount;
}

function zeros(n) {
  const xs = [];
  for (let i = 0; i < n; i++) {
    xs.push(0);
  }
  return xs;
}

function main() {
  seed = 7;
  const lines = [];
  const orders = [];
  for (let i = 0; i < 1000000; i++) {
    orders.push(makeOrder(i));
  }

  // Validate + enrich.
  const valid = orders.filter((o) => !o.refunded && o.unitPrice > 0);
  const totals = valid.map((o) => lineTotal(o));

  // Aggregate revenue per (region, category) and per customer.
  const cube = zeros(REGIONS.length * CATEGORIES.length);
  const perCustomer = zeros(CUSTOMERS);
  let revenue = 0;
  for (let i = 0; i < valid.length; i++) {
    const o = valid[i];
    const t = totals[i];
    cube[o.region * CATEGORIES.length + o.category] += t;
    perCustomer[o.customer] += t;
    revenue += t;
  }

  // Top 5 customers by spend (selection, no sort needed).
  const top = [];
  for (let k = 0; k < 5; k++) {
    let best = -1;
    for (let c = 0; c < CUSTOMERS; c++) {
      if (top.indexOf(c) === -1 && (best === -1 || perCustomer[c] > perCustomer[best])) {
        best = c;
      }
    }
    top.push(best);
  }

  lines.push(`orders: ${orders.length}, valid: ${valid.length}`);
  lines.push(`revenue: ${Math.round(revenue)}`);
  for (let r = 0; r < REGIONS.length; r++) {
    let best = 0;
    for (let c = 1; c < CATEGORIES.length; c++) {
      if (cube[r * CATEGORIES.length + c] > cube[r * CATEGORIES.length + best]) {
        best = c;
      }
    }
    lines.push(`${REGIONS[r]}: top category ${CATEGORIES[best]} (${Math.round(cube[r * CATEGORIES.length + best])})`);
  }
  lines.push(`top customers: ${top.join(", ")}`);
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
