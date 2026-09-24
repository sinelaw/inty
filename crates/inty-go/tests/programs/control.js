// Loops, labels, switch fallthrough, do-while with continue.
let total = 0;
for (let i = 0; i < 10; i++) {
  if (i % 2 === 0) {
    continue;
  }
  total += i;
}
console.log(total);

let k = 0;
do {
  k++;
  if (k < 3) {
    continue;
  }
  console.log(`do ${k}`);
} while (k < 5);

outer: for (let i = 0; i < 5; i++) {
  for (let j = 0; j < 5; j++) {
    if (i * j === 6) {
      console.log(`found ${i} ${j}`);
      break outer;
    }
  }
}

/** function describe(Number) => String */
function describe(n) {
  let out = "";
  switch (n) {
    case 0:
      out += "zero ";
    case 1:
      out += "small ";
      break;
    case 2:
    case 3:
      out += "medium ";
      break;
    default:
      out += "large ";
  }
  return out;
}
for (let n = 0; n < 5; n++) {
  console.log(describe(n));
}

let w = 1;
while (true) {
  w *= 3;
  if (w > 100) {
    break;
  }
}
console.log(w);
const t = w > 200 ? "big" : "small";
console.log(t);
