// Objects are typed structurally — by what fields they carry.
// `getName` works on *anything* with a `name` field.

function getName(obj) { return obj.name; }

var alice = getName({ name: "Alice", age: 30 });
var rover = getName({ name: "Rover", breed: "Labrador" });
var ship  = getName({ name: "USS Enterprise", warpFactor: 9 });

// Inty infers `getName(a) -> b where a has {name: b}` —
// only `name` is required; any other fields come along unchecked.
