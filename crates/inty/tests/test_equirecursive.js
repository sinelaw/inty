// Test equi-recursive types with 'this'
// Methods that reference their containing object create recursive types

// Example 1: Simple object with method using 'this'
var counter = {
    value: 0,
    add: function(x) {
        return this.value + x;
    }
};

var result1 = counter.add(5);  // 5

// Example 2: Multiple methods using 'this'
var point = {
    x: 10,
    y: 20,
    getX: function() {
        return this.x;
    },
    getY: function() {
        return this.y;
    },
    distanceFrom: function(other) {
        var dx = this.x - other.x;
        var dy = this.y - other.y;
        return dx * dx + dy * dy;
    }
};

var px = point.getX();  // 10
var py = point.getY();  // 20
var coordSum = px + py;  // 30 - forces px and py to be Number

var other = {x: 3, y: 4, getX: null, getY: null, distanceFrom: null};
var dist = point.distanceFrom(other);  // (10-3)^2 + (20-4)^2 = 305

// Example 3: Method that returns 'this' for chaining
var builder = {
    value: 0,
    setValue: function(v) {
        this.value = v;
        return this;
    },
    getValue: function() {
        return this.value;
    }
};

var val = builder.setValue(42).getValue();  // 42

// Example 4: Object with computed properties using 'this'
var rectangle = {
    width: 10,
    height: 20,
    area: function() {
        return this.width * this.height;
    },
    perimeter: function() {
        return 2 * (this.width + this.height);
    }
};

var area = rectangle.area();  // 200
var perim = rectangle.perimeter();  // 60

// Example 5: Factory function returning object with 'this' methods
function makeCounter(initial) {
    return {
        count: initial,
        increment: function() {
            this.count = this.count + 1;
            return this.count;
        },
        decrement: function() {
            this.count = this.count - 1;
            return this.count;
        },
        get: function() {
            return this.count;
        }
    };
}

var c1 = makeCounter(10);
c1.increment();
c1.increment();
var count = c1.get();  // 12

// Example 6: Methods calling other methods via 'this'
var calculator = {
    result: 0,
    add: function(n) {
        this.result = this.result + n;
        return this;
    },
    multiply: function(n) {
        this.result = this.result * n;
        return this;
    },
    compute: function() {
        return this.result;
    }
};

var calcResult = calculator.add(5).multiply(3).compute();  // 15

// Example 7: Nested object access via 'this'
var account = {
    balance: 1000,
    transactions: [],
    deposit: function(amount) {
        this.balance = this.balance + amount;
        return this.balance;
    },
    withdraw: function(amount) {
        this.balance = this.balance - amount;
        return this.balance;
    },
    getBalance: function() {
        return this.balance;
    }
};

account.deposit(500);
account.withdraw(200);
var finalBalance = account.getBalance();  // 1300

// The 'this' reference creates an equi-recursive type:
// The method's type references the object type (through 'this'),
// and the object type includes the method - a truly circular type definition!
