// minfern stdlib: minimal browser DOM.
//
// Embedded in the minfern binary and auto-loaded with the core library. Like
// core.d.js, this file is never executed by a JavaScript runtime, so
// `const x;` without an initializer is safe here.
//
// This is intentionally a small subset — enough to build a React-style SPA
// out of plain JS. Everything returned by `getElementById`/`createElement`
// collapses to a single "Element" shape because minfern has no union types,
// so we can't distinguish HTMLInputElement from HTMLDivElement etc. at the
// type level. That's a trade-off, not an oversight.

/** const document: {getElementById: (String) => {value: String, textContent: String, innerHTML: String, className: String, id: String, onclick: () => Undefined, oninput: () => Undefined, onchange: () => Undefined, onkeydown: ({key: String}) => Undefined, onkeyup: ({key: String}) => Undefined, onsubmit: () => Undefined}, createElement: (String) => {value: String, textContent: String, innerHTML: String, className: String, id: String, onclick: () => Undefined, oninput: () => Undefined, onchange: () => Undefined, onkeydown: ({key: String}) => Undefined, onkeyup: ({key: String}) => Undefined, onsubmit: () => Undefined}, title: String, location: {href: String, pathname: String, hash: String, search: String, reload: () => Undefined}} */
const document;

/** const window: {innerWidth: Number, innerHeight: Number} */
const window;

/** const setTimeout: (() => Undefined, Number) => Number */
const setTimeout;

/** const setInterval: (() => Undefined, Number) => Number */
const setInterval;

/** const clearTimeout: (Number) => Undefined */
const clearTimeout;

/** const clearInterval: (Number) => Undefined */
const clearInterval;

/** const alert: (String) => Undefined */
const alert;

// fetch and its minimum useful Response shape. `.json()` returns
// `Promise<T>` where T is polymorphic per call — callers usually
// pass the parsed result to code that fixes its shape via further
// property access.
/** const fetch: (String) => Promise<{status: Number, ok: Boolean, statusText: String, url: String, json: () => Promise<T>, text: () => Promise<String>}> */
const fetch;
