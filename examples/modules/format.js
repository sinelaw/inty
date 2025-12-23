// Pure formatting helpers. No dependency on store; imported by app.

export function formatCount(n) {
    return n === 1 ? "1 increment" : `${n} increments`;
}

export function formatHistory(history) {
    if (history.length === 0) return "no history";
    return history.map(n => `#${n}`).join(", ");
}
