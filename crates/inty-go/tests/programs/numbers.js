// Number -> string formatting and IEEE-754 arithmetic.
console.log(0.1 + 0.2);
const a = 0.1;
console.log(a + 0.2);
console.log(1 / 3);
console.log(-1 / 3);
console.log(1e21);
console.log(1e20);
console.log(123456789012345680000);
console.log(1.5e-7);
console.log(0.000001);
console.log(2 ** 53);
console.log(2 ** 64);
console.log(-0);
console.log(1 / 0);
console.log(-1 / 0);
const zero = 0;
console.log(zero / zero);
console.log(5e-324);
console.log(1.7976931348623157e308);
console.log(100);
console.log(-42.5);
console.log(Math.PI);
console.log(Math.PI / 180);
// Math.floor/ceil/trunc of an Int quotient: integer division, rounding
// like the double quotient does (toward -Infinity, +Infinity, zero).
const quotients = [[7, 2], [-7, 2], [7, -2], [-7, -2], [6, 3], [-6, 3], [0, -5], [9007199254740991, 3], [-9007199254740991, 2], [9007199254740990, 4503599627370495]];
for (const [a, b] of quotients) {
  console.log(`${a} ${b}: ${Math.floor(a / b)} ${Math.ceil(a / b)} ${Math.trunc(a / b)}`);
}
// A literal factor: the bound is checked on the other operand.
const factor = 4;
let prod = -3;
prod *= 5;
console.log(prod * 2 + 3 * prod + prod * factor + prod * -1);
