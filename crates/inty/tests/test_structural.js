// Test structural typing (duck typing)
// Functions work with any object that has the required shape

// Structural typing - more properties is compatible
function getName(obj) {
    return obj.name;
}

var person = {name: "Alice", age: 30};
var dog = {name: "Rover", breed: "Labrador"};
var product = {name: "Widget", price: 9.99};

var name1 = getName(person);   // "Alice"
var name2 = getName(dog);      // "Rover"
var name3 = getName(product);  // "Widget"


