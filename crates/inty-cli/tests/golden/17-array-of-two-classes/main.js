class Base { constructor(n) { this.n = n; } }
class Other { constructor() { this.n = 1; } }
const xs = [new Base(1), new Other()];
