// Polymorphic export. Used by `app-namespace.js` to demonstrate that a
// namespace import preserves the per-export polymorphism — two `ns.id`
// calls with different types must each type-check independently.

export function id(x) {
    return x;
}

export const PI = 3.14159;
