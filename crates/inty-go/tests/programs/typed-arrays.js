// Typed arrays: fixed-length arrays of int32, uint8 or float64.
function histogram(xs, buckets) {
  const h = new Int32Array(buckets);
  for (let i = 0; i < xs.length; i++) h[xs[i] % buckets] += 1;
  return h;
}
const h = histogram([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 4);
let line = "";
for (let i = 0; i < h.length; i++) line = line + String(h[i]) + " ";
console.log(line);

// A store wraps as ToInt32 / ToUint8 do.
const w = new Int32Array(3);
w[0] = 2147483647;
w[0] += 1;
w[1] = 2147483647 + 1;
w[2] = -7;
console.log(w[0] + w[1] + w[2]);
const bytes = Uint8Array.from([1, 2, 300, -1]);
bytes[0] |= 6;
bytes[1] ^= 3;
bytes[1] -= 5;
console.log(bytes[0] + bytes[1] + bytes[2] + bytes[3]);

// Float64Array, in a record, filled.
const holder = { data: new Float64Array(2).fill(0.5), name: "x" };
holder.data[0] += 1.25;
holder.data[1] = holder.data[0] * 2;
holder.data[1] /= 4;
console.log(holder.data[0] + holder.data[1]);
console.log(Float64Array.from([0.25, 2]).length);

// Identity and null, like any object.
const maybe = h.length > 10 ? h : null;
console.log(maybe === null);
console.log(h === h);
console.log(typeof h);
