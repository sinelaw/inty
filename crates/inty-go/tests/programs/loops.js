// Loops that hold arrays' slice headers in locals (see loops.rs), and
// the cases where they must not.

// A store that grows the array hands back the new header.
const xs = [1];
let s = 0;
for (let i = 0; i < 5; i++) {
  xs[xs.length] = i * 10;
  s += xs[xs.length - 1];
}
console.log(`${xs.length} ${s}`);

// Two names for one array: a grow through one must be seen by the other.
const a = [1, 2];
const b = a;
for (let i = 0; i < 4; i++) {
  a[a.length] = i;
  b[0] = b[0] + a.length;
}
console.log(`${a.length} ${b.length} ${a[0]} ${b[5]}`);

// A grow through a field is seen by a local name for the same array.
const holder = { items: [7] };
const items = holder.items;
let t = 0;
for (let i = 0; i < 3; i++) {
  holder.items[holder.items.length] = i;
  t += items[items.length - 1] + items.length;
}
console.log(`${t} ${items.length}`);

// A typed array reassigned by a function the loop calls.
let grid = new Int32Array(2);
function regrow() {
  grid = new Int32Array(grid.length + 1);
}
let lens = 0;
for (let i = 0; i < 3; i++) {
  regrow();
  grid[0] = i;
  lens += grid.length + grid[0];
}
console.log(lens);

// A typed array never reassigned, in a loop with calls.
const counts = new Int32Array(4);
function bucket(v) {
  return v % 4;
}
for (let i = 0; i < 10; i++) {
  counts[bucket(i)] += 1;
}
console.log(`${counts[0]} ${counts[1]} ${counts[2]} ${counts[3]}`);

// Labels, continue and break, nested loops.
const m = [3, 1, 4, 1, 5, 9, 2, 6];
let found = -1;
outer: for (let i = 0; i < m.length; i++) {
  for (let j = i + 1; j < m.length; j++) {
    if (m[i] + m[j] === 11) {
      found = i * 10 + j;
      break outer;
    }
    if (m[j] > m[i]) {
      continue outer;
    }
  }
}
console.log(found);

// A do-while that swaps elements in place.
const w = [5, 4, 3, 2, 1];
let k = 0;
do {
  const tmp = w[k];
  w[k] = w[w.length - 1 - k];
  w[w.length - 1 - k] = tmp;
  k++;
} while (k < 2);
console.log(`${w[0]} ${w[1]} ${w[2]} ${w[3]} ${w[4]}`);
