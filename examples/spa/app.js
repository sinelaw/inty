// inty-checked SPA: a classic todo list without React or any framework.
//
// State lives in a single plain object. Every event handler mutates that
// state and calls `render()`, which rebuilds the list portion of the DOM
// from an HTML string and re-attaches per-item handlers.
//
// To type-check:
//     inty examples/spa/app.js
//
// Features exercised (every one produced by inty's regular inference —
// no body annotations anywhere except the single `state` declaration):
//   - Embedded stdlib (document, console, Math, JSON, Object, Array, ...)
//   - Function hoisting: `render()` is defined at the bottom, called from
//     closures created near the top.
//   - Arrow functions, `let`, `const`.
//   - Object destructuring in function parameters' bodies.
//   - Inline `/*: T */` annotation on `state` to seed a typed empty
//     collection.
//   - Array.prototype / String.prototype built-ins (filter, map, forEach,
//     some, reduce, replaceAll, ...).
//   - async / await and Promise<T> for the "Save" button demo.

// ---------------------------------------------------------------------------
// State. Each field carries its own inline annotation, which pins the
// element type of `todos` so we can start empty (without it, `todos: []`
// would be inferred as `a[]` until the first push). The extra
// `todos.push(...)` calls below seed a couple of rows of initial content
// without fighting the type.
// ---------------------------------------------------------------------------

let x = 3;
//let y = x + 'a';

function test(x) {
if (x > 4) {
return 'bad';
} else {
    return x;
}
}

function moshe(x) {
    let res = test(x);
    
    if (typeof(res) == 'number') {
        return 'cool';
    } else
    if (typeof(res) == 'boolean') {
        return 'bad';
    }
}

let state = {
    todos  /*: {id: Number, text: String, done: Boolean}[] */: [],
    nextId /*: Number */: 1,
    filter /*: String */: "all"
};
//state.moshe = state.yosi;

state.todos.push({id: 1, text: "Try editing this todo list", done: false});
state.todos.push({id: 2, text: "Read examples/spa/app.js", done: true});
state.nextId = 3;

// Save counter, bumped every time the async save completes.
let saveCounter = 0;

// ---------------------------------------------------------------------------
// Pure helpers.
// ---------------------------------------------------------------------------

function escapeHtml(s) {
    return s
        .replaceAll("&", "&amp;")
        .replaceAll("<", "&lt;")
        .replaceAll(">", "&gt;")
        .replaceAll("\"", "&quot;")
        .replaceAll("'", "&#39;");
}

function countRemaining() {
    return state.todos.filter(t => !t.done).length;
}

function hasAnyDone() {
    return state.todos.some(t => t.done);
}

function shouldShow(todo) {
    if (state.filter === "active") return !todo.done;
    if (state.filter === "done") return todo.done;
    return true;
}

// ---------------------------------------------------------------------------
// State updates.
// ---------------------------------------------------------------------------

function addTodo(text) {
    if (text === "") return;
    state.todos.push({id: state.nextId, text: text, done: false});
    state.nextId = state.nextId + 1;
}

function toggleTodo(id) {
    state.todos.forEach(t => {
        if (t.id === id) t.done = !t.done;
        return undefined;
    });
}

function deleteTodo(id) {
    state.todos = state.todos.filter(t => t.id !== id);
}

function clearDone() {
    state.todos = state.todos.filter(t => !t.done);
}

function setFilter(f) {
    state.filter = f;
}

// ---------------------------------------------------------------------------
// Rendering. The list and footer are rebuilt from scratch on every update.
// ---------------------------------------------------------------------------

function renderTodoItem(todo) {
    const {id, text, done} = todo;
    const liClass = done ? "done" : "";
    const toggleClass = done ? "toggle on" : "toggle";
    const toggleMark = done ? "✓" : "";
    return (
        `<li class="${liClass}">` +
            `<button id="toggle-${id}" class="${toggleClass}">${toggleMark}</button>` +
            `<span class="text">${escapeHtml(text)}</span>` +
            `<button id="delete-${id}" class="delete" title="Delete">×</button>` +
        `</li>`
    );
}

function renderList() {
    const listEl = document.getElementById("todo-list");
    const visible = state.todos.filter(shouldShow);
    let html = "";
    if (visible.length === 0) {
        html = state.todos.length === 0
            ? `<li class="empty">No todos yet. Add one above.</li>`
            : `<li class="empty">Nothing matches the current filter.</li>`;
    } else {
        html = visible.map(renderTodoItem).join("");
    }
    listEl.innerHTML = html;
}

function renderFooter() {
    const footer = document.getElementById("footer");
    const remaining = countRemaining();
    const word = remaining === 1 ? "item" : "items";
    const clearMarkup = hasAnyDone()
        ? `<button id="clear-done">Clear completed</button>`
        : `<span></span>`;
    footer.innerHTML = `<span>${remaining} ${word} left</span>` + clearMarkup;
}

function renderFilters() {
    ["all", "active", "done"].forEach(name => {
        document.getElementById(`filter-${name}`).className =
            state.filter === name ? "active" : "";
        return undefined;
    });
}

function attachListHandlers() {
    state.todos.forEach(todo => {
        if (shouldShow(todo)) {
            const {id} = todo;
            document.getElementById(`toggle-${id}`).onclick = () => {
                toggleTodo(id);
                render();
                return undefined;
            };
            document.getElementById(`delete-${id}`).onclick = () => {
                deleteTodo(id);
                render();
                return undefined;
            };
        }
        return undefined;
    });
    if (hasAnyDone()) {
        document.getElementById("clear-done").onclick = () => {
            clearDone();
            render();
            return undefined;
        };
    }
}

function render() {
    renderList();
    renderFooter();
    renderFilters();
    attachListHandlers();
}

// ---------------------------------------------------------------------------
// Async "save" demo. Stands in for a `fetch("/api/todos", {method: "POST"})`
// call — we just resolve an immediate Promise so the example runs over
// file://. The button's status label gets an intermediate "Saving..." so
// you can see the await actually suspend the handler.
// ---------------------------------------------------------------------------

async function persistTodos() {
    const payload = JSON.stringify(state.todos);
    // In a real app this would be `await fetch("/api/todos", ...)`. fetch is
    // available in the stdlib; it returns `Promise<Response>`.
    await Promise.resolve(0);
    return payload.length;
}

async function save() {
    const statusEl = document.getElementById("save-status");
    statusEl.textContent = "Saving…";
    const bytes = await persistTodos();
    saveCounter = saveCounter + 1;
    statusEl.textContent = `Saved ${bytes} bytes (${saveCounter})`;
    return undefined;
}

// ---------------------------------------------------------------------------
// Top-level wiring: the four static elements that live for the whole session.
// ---------------------------------------------------------------------------

function submitDraft() {
    const input = document.getElementById("new-input");
    addTodo(input.value);
    input.value = "";
    render();
}

document.getElementById("add-btn").onclick = () => {
    submitDraft();
    return undefined;
};

document.getElementById("new-input").onkeydown = e => {
    if (e.key === "Enter") submitDraft();
    return undefined;
};

["all", "active", "done"].forEach(name => {
    document.getElementById(`filter-${name}`).onclick = () => {
        setFilter(name);
        render();
        return undefined;
    };
    return undefined;
});

document.getElementById("save-btn").onclick = () => {
    // `save()` returns a Promise<Undefined>; we don't await it here since
    // top-level await isn't something inty enforces yet, and we don't
    // need the result.
    save();
    return undefined;
};

render();
