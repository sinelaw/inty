// Class declarations desugar to factory functions returning a row of
// methods + fields. `#name` private fields lower to a sentinel key —
// unreachable from outside.

class Counter {
    #count = 0;
    inc() {
        this.#count = this.#count + 1;
        return this.#count;
    }
    get current() { return this.#count; }
}

var c = new Counter();
var n = c.inc();           // Number
var v = c.current;         // Number

// Try this — uncomment to see the parse error:
// var leak = c.#count;
