// Unit test for 'this' in methods - verifying return types are concrete
// This tests that methods using 'this' return the correct concrete types

// Test 1: Simple getter should return Number
var obj1 = {
    x: 10,
    getX: function() {
        return this.x;
    }
};

var val1 = obj1.getX();
var val2 = val1 + 5;  // Should work - val1 should be Number

// Test 2: Multiple getters
var obj2 = {
    x: 10,
    y: 20,
    getX: function() {
        return this.x;
    },
    getY: function() {
        return this.y;
    }
};

var x = obj2.getX();
var y = obj2.getY();
var sum = x + y;  // Both should be Number

// Test 3: Method returning computed value
var rect = {
    width: 10,
    height: 20,
    getArea: function() {
        return this.width * this.height;
    }
};

var area = rect.getArea();
var doubled = area * 2;  // area should be Number

// Test 4: Method chaining - intermediate results should have concrete types
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

var c = counter.increment().increment();
var finalValue = c.get();
var result = finalValue + 10;  // finalValue should be Number

// Test 5: Method using 'this' field in computation
var calculator = {
    base: 10,
    add: function(x) {
        return this.base + x;
    }
};

var res1 = calculator.add(5);
var res2 = res1 * 2;  // res1 should be Number

// Test 6: String fields
var person = {
    name: "Alice",
    getName: function() {
        return this.name;
    }
};

var name = person.getName();
var greeting = "Hello, " + name;  // name should be String

// Test 7: Factory function
function makePoint(x, y) {
    return {
        x: x,
        y: y,
        getX: function() {
            return this.x;
        },
        getY: function() {
            return this.y;
        }
    };
}

var p = makePoint(3, 4);
var px = p.getX();
var py = p.getY();
var dist = px * px + py * py;  // px and py should be Number

// Test 8: Method returning different field type
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
var check1 = num + 1;  // num should be Number
var check2 = str + "!";  // str should be String
