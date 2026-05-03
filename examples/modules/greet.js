// Default-export demo. Each module here exports exactly one thing — a
// greeting function and a constant — and `app-default.js` next door
// imports them by whatever local name it likes.

export default function greet(name) {
    return `hi ${name}`;
}
