// Pulling a method off an object loses `this`. TypeScript with default
// settings types it as a plain function and lets you call it standalone.
// At runtime it explodes — `this` is undefined.
//
// Inty: `this` is part of the method's row type. The free function and
// the bound method aren't interchangeable.

var counter = {
    n: 0,
    inc: function() { this.n = this.n + 1; return this.n; }
};

var inc = counter.inc;
// var oops = inc();          // ← uncomment: at runtime, TypeError.
//                             //   Inty rejects at type-check time.

var ok = counter.inc();
