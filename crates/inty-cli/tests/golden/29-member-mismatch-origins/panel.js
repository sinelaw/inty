// `source.count * 2` reads `count` as a number.
let source;
export class Counter {
  constructor(s) { source = s; }
  total() { return source.count * 2; }
}
