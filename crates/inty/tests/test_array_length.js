// Test array.length property access
var arr = [1, 2, 3];
var len = arr.length;

// Should work in loops
for (var i = 0; i < arr.length; i++) {
    var x = arr[i];
}

// Empty array
var empty = [];
var emptyLen = empty.length;

// Array with function creating it
function makeArray() {
    return [1, 2, 3];
}
var arrLen = makeArray().length;

// Polymorphic function that accesses .length
// Array<T> unifies with {length: Number | a} constraint
function getLength(arr) {
    return arr.length;
}
var numbers = [1, 2, 3];
var numLen = getLength(numbers);

// Higher-order function using both .length and indexing
function map(arr, fn) {
    var result = [];
    for (var i = 0; i < arr.length; i++) {
        result[i] = fn(arr[i]);
    }
    return result;
}
var doubled = map([1, 2, 3], function(x) { return x * 2; });
