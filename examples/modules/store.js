// Shared state + mutations. Exports a single mutable `state` binding and a
// handful of functions that operate on it. The importing file uses the same
// names directly — inty's module resolver threads types through `export`
// and `import` without any annotations on the import side.

/** export let state: {
    count: Number,
    history: Number[]
} */
export let state = {count: 0, history: []};

export function increment() {
    state.count = state.count + 1;
    state.history.push(state.count);
}

export function reset() {
    state.count = 0;
    state.history = [];
}

export function snapshot() {
    return {count: state.count, history: state.history};
}
