// Demonstrates `export { … }` and renaming. The two locals stay private
// under their internal names — `square` and `cube` are only visible to
// importers via the explicit export list.

function square(n) {
    return n * n;
}

function cube(n) {
    return n * n * n;
}

// `square` exported under its own name; `cube` renamed to `pow3`.
export { square, cube as pow3 };
