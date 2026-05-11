// Objects are typed structurally — by what fields they carry.
// `getName` works on *anything* with a `name` field.

function getName(obj) { return obj.name; }

var alice = getName({ name: "Alice", age: 30 });
var rover = getName({ name: "Rover", breed: "Labrador" });
var ship  = getName({ name: "USS Enterprise", warpFactor: 9 });

// Inty infers `getName<a, b>({name: a | b}) => a` —
// only `name` is required; the row variable `b` carries the rest.
