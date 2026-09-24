// Higher-order array methods: map / filter / reduce with closures,
// rebuilt on every round.
function range(n) {
  const xs = [];
  for (let i = 0; i < n; i++) {
    xs.push(i);
  }
  return xs;
}

const xs = range(100000);
let total = 0;
for (let round = 0; round < 300; round++) {
  const squares = xs.map((x) => x * x + round);
  const odd = squares.filter((x) => x % 2 === 1);
  total += odd.reduce((acc, x) => acc + x / 1000, 0);
}
console.log(total);
