// A tagged union — a single value that's exactly one of N known shapes.
// `shape.kind === "..."` refines the type inside each branch.

/** function area(s: {kind: "circle", r: Number}
                 | {kind: "square", s: Number}) => Number */
function area(shape) {
    if (shape.kind === "circle") {
        return shape.r;             // shape narrowed to circle
    } else {
        return shape.s;             // shape narrowed to square
    }
}

var a = area({ kind: "circle", r: 10 });
var b = area({ kind: "square", s:  5 });
