// Longest Collatz chain below a bound: integer arithmetic done in
// doubles, dominated by `%` and division.
function chainLength(start) {
  let n = start;
  let steps = 1;
  while (n !== 1) {
    if (n % 2 === 0) {
      n = n / 2;
    } else {
      n = 3 * n + 1;
    }
    steps++;
  }
  return steps;
}

let best = 0;
let bestStart = 0;
for (let i = 1; i < 2000000; i++) {
  const len = chainLength(i);
  if (len > best) {
    best = len;
    bestStart = i;
  }
}
console.log(`${bestStart} ${best}`);
