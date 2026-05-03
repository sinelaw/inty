// Internal helpers. None of these are imported directly by `app-reexport.js`
// — they pass through the public-surface module `lib.js` next door.

export function double(n) {
    return n + n;
}

export function triple(n) {
    return n + n + n;
}

export const TAG = "internal-v1";

export default function describe() {
    return `lib (${TAG})`;
}
