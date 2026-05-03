// Unit test for 'this' method return types
// Tests that methods return concrete types when object fields are concrete

function assert(condition, message) {
    if (!condition) {
        throw "Assertion failed: " + message;
    }
}

// Test 1: Method should return concrete Number
var obj = {
    x: 10,
    getX: function() {
        return this.x;
    }
};

var result = obj.getX();
assert(result === 10, "getX should return 10");
assert(typeof result === "number", "getX should return number type");

// Test 2: Two getters should both return concrete Numbers
var point = {
    x: 10,
    y: 20,
    getX: function() {
        return this.x;
    },
    getY: function() {
        return this.y;
    }
};

var x = point.getX();
var y = point.getY();
assert(x === 10, "getX should return 10");
assert(y === 20, "getY should return 20");
assert(x + y === 30, "x + y should be 30");

// Test 3: Method returning computed Number
var rect = {
    width: 10,
    height: 20,
    area: function() {
        return this.width * this.height;
    }
};

var area = rect.area();
assert(area === 200, "area should be 200");

// Test 4: Method returning String
var person = {
    name: "Alice",
    getName: function() {
        return this.name;
    }
};

var name = person.getName();
assert(name === "Alice", "getName should return Alice");

// Test 5: Method with parameter returning Number
var calculator = {
    base: 10,
    add: function(x) {
        return this.base + x;
    }
};

var sum = calculator.add(5);
assert(sum === 15, "add(5) should return 15");

// Test 6: Method chaining
var counter = {
    value: 0,
    increment: function() {
        this.value = this.value + 1;
        return this;
    },
    get: function() {
        return this.value;
    }
};

var finalValue = counter.increment().increment().get();
assert(finalValue === 2, "after two increments, value should be 2");

// Test 7: Factory function with methods
function makePoint(x, y) {
    return {
        x: x,
        y: y,
        getX: function() {
            return this.x;
        },
        getY: function() {
            return this.y;
        },
        sum: function() {
            return this.x + this.y;
        }
    };
}

var p = makePoint(3, 4);
assert(p.getX() === 3, "getX should return 3");
assert(p.getY() === 4, "getY should return 4");
assert(p.sum() === 7, "sum should return 7");

// Test 8: Multiple field types
var mixed = {
    count: 42,
    label: "answer",
    getCount: function() {
        return this.count;
    },
    getLabel: function() {
        return this.label;
    }
};

var num = mixed.getCount();
var str = mixed.getLabel();
assert(num === 42, "getCount should return 42");
assert(str === "answer", "getLabel should return 'answer'");
