// Arithmetic, remainder, bitwise and comparison operators.
function show(x) {
  console.log(x);
}
show(7 % 3);
show(-7 % 3);
show(7 % -3);
show(5.5 % 2);
const big = 4294967296 + 5;
show(big | 0);
show(-1 >>> 0);
show(-16 >> 2);
show(1 << 31);
show(~5);
show(0xff & 0x0f);
show(6 ^ 3);
show(2 ** 10);
show(Math.round(2.5));
show(Math.round(-2.5));
show(Math.floor(-1.5));
show(Math.max(3, 7));
show(Math.imul(123456789, 987654321));
console.log(3 < 4 && 4 <= 4);
console.log("abc" < "abd");
console.log(1 === 1.0);
let n = 10;
n -= 3;
n *= 2;
n /= 7;
n %= 3;
n **= 3;
show(n);
let bits = 5;
bits <<= 2;
bits |= 1;
bits >>>= 1;
show(bits);
