// Test polymorphic (generic) functions
// Shows how functions can work with multiple types

// Polymorphic identity function
function identity(x) {
    return x;
}

var num = identity(42);
var str = identity("hello");
var obj = identity({foo: 1, bar: 2});
var arr = identity([1, 2, 3]);

// Nested function calls (closures)
function outer(x) {
    function inner(y) {
        return x + y;
    }
    return inner;
}

var addThree = outer(3);
var result3 = addThree(7);  // 10

// Example 7: Polymorphic pair functions
function makePair(first, second) {
    return {first: first, second: second};
}

var numPair = makePair(1, 2);
var strPair = makePair("hello", "world");
var mixedPair = makePair(42, "answer");

var firstNum = numPair.first;  // 1
var secondStr = strPair.second;  // "world"

// Example 9: Polymorphic array builder
function makeArray(a, b, c) {
    return [a, b, c];
}

var numbers = makeArray(1, 2, 3);
var strings = makeArray("a", "b", "c");

// Example 10: Polymorphic getter
function getFirst(obj) {
    return obj.first;
}

var pair1First = getFirst(numPair);
var pair2First = getFirst(strPair);

// Example 11: Polymorphic object builder
function makeTriple(x, y, z) {
    return {x: x, y: y, z: z};
}

var point3d = makeTriple(1, 2, 3);
var names = makeTriple("Alice", "Bob", "Charlie");
