class Counter {
    #count = 0;
    inc() {
        this.#count = this.#count + 1;
        return this.#count;
    }
    get current() { return this.#count; }
}

var c = new Counter();
var leak = c.#count;     // ← should be parse / type error
