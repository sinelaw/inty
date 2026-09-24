// String operations over ASCII text.
const greeting = "Hello";
const name = "world";
const msg = greeting + ", " + name + "!";
console.log(msg);
console.log(msg.length);
console.log(`${greeting.toUpperCase()} ${name.length} ${true} ${1.5}`);
console.log(msg.slice(7, 12));
console.log(msg.substring(0, 5));
console.log(msg.indexOf("world"));
console.log(msg.charCodeAt(0));
console.log(String.fromCharCode(65));
console.log(msg[4]);
let acc = "";
for (let i = 0; i < 5; i++) {
  acc += String(i);
}
console.log(acc);
console.log(typeof acc);
console.log(["a", "b", "c"].join(""));
console.log([1.5, 2, 3].join(", "));
