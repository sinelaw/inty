// Smoke test for Promise<T> + async/await type inference.

// Promise.resolve is polymorphic: each call instantiates T fresh.
var pn = Promise.resolve(42);       // Promise<Number>
var ps = Promise.resolve("ok");     // Promise<String>
var pb = Promise.resolve(true);     // Promise<Boolean>

// Promise.reject keeps the payload type polymorphic.
var bad = Promise.reject("boom");

// .then — callback must return Promise<U>, result is Promise<U>.
var doubled = pn.then(function(n) { return Promise.resolve(n * 2); });

// Chained .then.
var chained = pn
    .then(function(n) { return Promise.resolve(n + 1); })
    .then(function(n) { return Promise.resolve(n * 10); });

// .catch — recover to Promise<T> again.
var recovered = pn.catch(function(e) { return Promise.resolve(0); });

// .finally — no-arg callback returning Undefined.
var done = pn.finally(function() { return undefined; });

// Promise.all([Promise<T>]) => Promise<T[]>.
var all = Promise.all([pn, Promise.resolve(7), Promise.resolve(9)]);

// async function wraps its return in Promise<T>.
async function double(n) {
    var v = await pn;
    return v * 2;
}
var d = double(5);  // Promise<Number>

// await on a Promise<T> gives T; chaining awaits through nested asyncs.
async function sum() {
    var xs = await all;       // xs: Number[]
    var head = xs[0];         // Number
    var next = await double(head);  // await Promise<Number> => Number
    return head + next;
}

// fetch returns a Promise<Response>; .json() returns Promise<T>.
async function fetchJson(path) {
    var res = await fetch(path);
    return res.status;        // Number
}
