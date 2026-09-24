// Closures, higher-order functions, nested and recursive functions.
function makeCounter() {
  let count = 0;
  return () => {
    count++;
    return count;
  };
}
const next = makeCounter();
next();
next();
console.log(next());

const fns = [];
for (let i = 0; i < 3; i++) {
  fns.push(() => i * 10);
}
console.log(fns.map((f) => f()).join(","));

function sumTo(n) {
  function go(i, acc) {
    if (i > n) {
      return acc;
    }
    return go(i + 1, acc + i);
  }
  return go(1, 0);
}
console.log(sumTo(100));

const xs = [5, 3, 8, 1];
console.log(xs.filter((x) => x > 2).map((x) => x * 2).reduce((a, b) => a + b, 0));
console.log(xs.some((x) => x === 8));
console.log(xs.every((x) => x > 0));
console.log(xs.findIndex((x) => x === 8));
xs.forEach((x) => {
  console.log(x);
});

function apply(f, x) {
  return f(f(x));
}
console.log(apply((v) => v + 1, 40));
