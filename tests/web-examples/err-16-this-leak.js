var counter = {
    n: 0,
    inc: function() { this.n = this.n + 1; return this.n; }
};

var inc = counter.inc;
var oops = inc();          // ← should be a type error
