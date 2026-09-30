class Counter {
  constructor(start) { this.count = start; }
  next() { return this.count + 1; }
}
/** function current(c: Counter) => Number */
function current(c) { return c.count; }
