// Sieve of Eratosthenes, repeated: array-of-booleans writes and reads
// with integer-valued indices.
function sieve(n) {
  const composite = [];
  for (let i = 0; i <= n; i++) {
    composite.push(false);
  }
  let count = 0;
  for (let i = 2; i <= n; i++) {
    if (!composite[i]) {
      count++;
      for (let j = i * i; j <= n; j += i) {
        composite[j] = true;
      }
    }
  }
  return count;
}

let total = 0;
for (let round = 0; round < 20; round++) {
  total += sieve(2000000);
}
console.log(total);
