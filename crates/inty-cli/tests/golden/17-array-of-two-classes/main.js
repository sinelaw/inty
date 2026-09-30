class Base { constructor(n) { this.n = n; } }
class Sub extends Base { constructor() { super(1); } }
const xs = [new Base(1), new Sub()];
