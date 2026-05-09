// inty stdlib: minimal browser DOM.
//
// Embedded in the inty binary and auto-loaded with the core library. Like
// core.d.js, this file is never executed by a JavaScript runtime, so
// `const x;` without an initializer is safe here.
//
// This is intentionally a small subset — enough to build a React-style SPA
// out of plain JS. Everything returned by `getElementById`/`createElement`
// collapses to a single "Element" shape because inty has no union types,
// so we can't distinguish HTMLInputElement from HTMLDivElement etc. at the
// type level. That's a trade-off, not an oversight.
//
// inty's type aliases don't yet support direct self-recursion (see
// examples/spa/gaps.md), so methods that "return an Element-like
// thing" like `cloneNode` or `closest` get a fresh row variable T per
// call site. Callers can still chain methods on the result because of
// row polymorphism.

/** const document: <T>{
        getElementById: (String) => {
            value: String, textContent: String, innerHTML: String, outerHTML: String,
            className: String, id: String, hidden: Boolean, disabled: Boolean,
            checked: Boolean, autofocus: Boolean, loading: String, tabIndex: Number,
            offsetWidth: Number, offsetHeight: Number, offsetTop: Number, offsetLeft: Number,
            scrollWidth: Number, scrollHeight: Number, scrollTop: Number, scrollLeft: Number,
            clientWidth: Number, clientHeight: Number, nodeName: String, tagName: String,
            onclick: () => Undefined, oninput: () => Undefined, onchange: () => Undefined,
            onkeydown: ({key: String}) => Undefined, onkeyup: ({key: String}) => Undefined,
            onsubmit: () => Undefined, onload: () => Undefined,
            classList: {
                add: (String) => Undefined, remove: (String) => Undefined,
                toggle: (String) => Boolean, contains: (String) => Boolean,
                replace: (String, String) => Boolean
            },
            setAttribute: (String, String) => Undefined,
            getAttribute: (String) => String,
            hasAttribute: (String) => Boolean,
            removeAttribute: (String) => Undefined,
            toggleAttribute: (String) => Boolean,
            addEventListener: (String, (T) => Undefined) => Undefined,
            removeEventListener: (String, (T) => Undefined) => Undefined,
            dispatchEvent: (T) => Boolean,
            querySelector: (String) => T,
            querySelectorAll: (String) => T[],
            closest: (String) => T,
            matches: (String) => Boolean,
            contains: (T) => Boolean,
            cloneNode: (Boolean) => T,
            appendChild: (T) => T,
            removeChild: (T) => T,
            replaceChild: (T, T) => T,
            insertBefore: (T, T) => T,
            before: (T) => Undefined, after: (T) => Undefined,
            append: (T) => Undefined, prepend: (T) => Undefined,
            remove: () => Undefined, replaceWith: (T) => Undefined,
            getBoundingClientRect: () => {top: Number, right: Number, bottom: Number, left: Number, width: Number, height: Number, x: Number, y: Number},
            scrollIntoView: () => Undefined,
            focus: () => Undefined, blur: () => Undefined,
            click: () => Undefined,
            submit: () => Undefined, requestSubmit: () => Undefined, reset: () => Undefined,
            showModal: () => Undefined, show: () => Undefined, close: () => Undefined,
            open: Boolean,
            children: T[], parentElement: T,
            firstElementChild: T, lastElementChild: T,
            nextElementSibling: T, previousElementSibling: T,
            style: {
                setProperty: (String, String) => Undefined,
                removeProperty: (String) => String,
                getPropertyValue: (String) => String
            },
            form: T
        },
        createElement: (String) => {
            value: String, textContent: String, innerHTML: String, outerHTML: String,
            className: String, id: String, hidden: Boolean, disabled: Boolean,
            checked: Boolean, autofocus: Boolean, loading: String, tabIndex: Number,
            offsetWidth: Number, offsetHeight: Number, offsetTop: Number, offsetLeft: Number,
            scrollWidth: Number, scrollHeight: Number, scrollTop: Number, scrollLeft: Number,
            clientWidth: Number, clientHeight: Number, nodeName: String, tagName: String,
            onclick: () => Undefined, oninput: () => Undefined, onchange: () => Undefined,
            onkeydown: ({key: String}) => Undefined, onkeyup: ({key: String}) => Undefined,
            onsubmit: () => Undefined, onload: () => Undefined,
            classList: {
                add: (String) => Undefined, remove: (String) => Undefined,
                toggle: (String) => Boolean, contains: (String) => Boolean,
                replace: (String, String) => Boolean
            },
            setAttribute: (String, String) => Undefined,
            getAttribute: (String) => String,
            hasAttribute: (String) => Boolean,
            removeAttribute: (String) => Undefined,
            toggleAttribute: (String) => Boolean,
            addEventListener: (String, (T) => Undefined) => Undefined,
            removeEventListener: (String, (T) => Undefined) => Undefined,
            dispatchEvent: (T) => Boolean,
            querySelector: (String) => T,
            querySelectorAll: (String) => T[],
            closest: (String) => T,
            matches: (String) => Boolean,
            contains: (T) => Boolean,
            cloneNode: (Boolean) => T,
            appendChild: (T) => T,
            removeChild: (T) => T,
            replaceChild: (T, T) => T,
            insertBefore: (T, T) => T,
            before: (T) => Undefined, after: (T) => Undefined,
            append: (T) => Undefined, prepend: (T) => Undefined,
            remove: () => Undefined, replaceWith: (T) => Undefined,
            getBoundingClientRect: () => {top: Number, right: Number, bottom: Number, left: Number, width: Number, height: Number, x: Number, y: Number},
            scrollIntoView: () => Undefined,
            focus: () => Undefined, blur: () => Undefined,
            click: () => Undefined,
            submit: () => Undefined, requestSubmit: () => Undefined, reset: () => Undefined,
            showModal: () => Undefined, show: () => Undefined, close: () => Undefined,
            open: Boolean,
            children: T[], parentElement: T,
            firstElementChild: T, lastElementChild: T,
            nextElementSibling: T, previousElementSibling: T,
            style: {
                setProperty: (String, String) => Undefined,
                removeProperty: (String) => String,
                getPropertyValue: (String) => String
            },
            form: T
        },
        querySelector: (String) => T,
        querySelectorAll: (String) => T[],
        addEventListener: (String, (T) => Undefined) => Undefined,
        removeEventListener: (String, (T) => Undefined) => Undefined,
        dispatchEvent: (T) => Boolean,
        head: T,
        body: T,
        documentElement: T,
        activeElement: T,
        title: String,
        cookie: String,
        location: {
            href: String, pathname: String, hash: String, search: String,
            origin: String, host: String, hostname: String, protocol: String, port: String,
            reload: () => Undefined,
            assign: (String) => Undefined,
            replace: (String) => Undefined
        }
    } */
const document;

/** const window: <T>{
        innerWidth: Number,
        innerHeight: Number,
        scrollX: Number,
        scrollY: Number,
        pageXOffset: Number,
        pageYOffset: Number,
        devicePixelRatio: Number,
        visualViewport: {width: Number, height: Number, offsetLeft: Number, offsetTop: Number, pageLeft: Number, pageTop: Number, scale: Number, addEventListener: (String, (T) => Undefined) => Undefined, removeEventListener: (String, (T) => Undefined) => Undefined},
        addEventListener: (String, (T) => Undefined) => Undefined,
        removeEventListener: (String, (T) => Undefined) => Undefined,
        dispatchEvent: (T) => Boolean,
        location: {
            href: String, pathname: String, hash: String, search: String,
            origin: String, host: String, hostname: String, protocol: String, port: String,
            reload: () => Undefined,
            assign: (String) => Undefined,
            replace: (String) => Undefined
        },
        scrollTo: (Number, Number) => Undefined,
        scrollBy: (Number, Number) => Undefined,
        getComputedStyle: (T) => {getPropertyValue: (String) => String},
        requestAnimationFrame: ((Number) => Undefined) => Number,
        cancelAnimationFrame: (Number) => Undefined,
        matchMedia: (String) => {matches: Boolean, addEventListener: (String, (T) => Undefined) => Undefined}
    } */
const window;

// Browser navigator. Subset of the most-used capability flags and
// permission-gated subsystems; everything is non-nullable in inty's
// type system, so callers that branch on availability must do so at
// runtime, but the access itself type-checks.
/** const navigator: <T, U>{
        userAgent: String,
        language: String,
        languages: String[],
        onLine: Boolean,
        maxTouchPoints: Number,
        clipboard: {
            writeText: (String) => Promise<Undefined>,
            readText: () => Promise<String>
        },
        credentials: {
            create: (T) => Promise<U>,
            get: (T) => Promise<U>
        },
        serviceWorker: {
            register: (String) => Promise<T>,
            getRegistration: () => Promise<T>
        },
        setAppBadge: (Number) => Promise<Undefined>,
        clearAppBadge: () => Promise<Undefined>
    } */
const navigator;

// AbortController. The signal it produces is opaque (T) because
// modelling AbortSignal as a row that contains itself isn't possible
// without self-recursion.
/** const AbortController: <T>() => {signal: T, abort: () => Undefined} */
const AbortController;

// FormData / URLSearchParams. Construct from a form Element or with no
// arguments; both expose the same get/set/append surface.
/** const FormData: <T>(T) => {
        get: (String) => String,
        getAll: (String) => String[],
        has: (String) => Boolean,
        set: (String, String) => Undefined,
        append: (String, String) => Undefined,
        delete: (String) => Undefined
    } */
const FormData;

/** const URLSearchParams: () => {
        get: (String) => String,
        getAll: (String) => String[],
        has: (String) => Boolean,
        set: (String, String) => Undefined,
        append: (String, String) => Undefined,
        delete: (String) => Undefined,
        toString: () => String
    } */
const URLSearchParams;

// Text encoding/decoding. `encode`/`decode` cover the vast majority of
// real-world uses; the streaming variants (`encodeInto`, `decode` with
// options) are out of scope for this stdlib.
/** const TextDecoder: <T>() => {decode: (T) => String} */
const TextDecoder;

/** const TextEncoder: <T>() => {encode: (String) => T} */
const TextEncoder;

// CustomEvent / Event. Constructors take an `init` row (`detail`,
// `bubbles`, …); the resulting object exposes the read-only fields
// the rest of the DOM expects on event objects. `target` is opaque
// (T) since it could be any Element-shaped value.
/** const CustomEvent: <T, U, V>(String, T) => {type: String, detail: U, bubbles: Boolean, defaultPrevented: Boolean, target: V, currentTarget: V, preventDefault: () => Undefined, stopPropagation: () => Undefined, stopImmediatePropagation: () => Undefined} */
const CustomEvent;

/** const Event: <V>(String) => {type: String, bubbles: Boolean, defaultPrevented: Boolean, target: V, currentTarget: V, preventDefault: () => Undefined, stopPropagation: () => Undefined, stopImmediatePropagation: () => Undefined} */
const Event;

// Custom-element registry. `define` is the only widely-used method; the
// constructor argument is opaque (T) because inty has no class
// inheritance and can't represent the `extends HTMLElement` constraint
// the platform requires.
/** const customElements: <T>{
        define: (String, T) => Undefined,
        get: (String) => T,
        whenDefined: (String) => Promise<T>
    } */
const customElements;

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

// Window globals also available bare under `globalThis`. Most code
// reaches them via `window.X`, but a few helpers (e.g. fizzy's
// scroll_helpers) call `getComputedStyle(el)` directly.
/** const getComputedStyle: <T>(T) => {getPropertyValue: (String) => String} */
const getComputedStyle;

/** const requestAnimationFrame: ((Number) => Undefined) => Number */
const requestAnimationFrame;

/** const cancelAnimationFrame: (Number) => Undefined */
const cancelAnimationFrame;

// fetch and its minimum useful Response shape. `.json()` returns
// `Promise<T>` where T is polymorphic per call — callers usually
// pass the parsed result to code that fixes its shape via further
// property access.
/** const fetch: <T>(String) => Promise<{status: Number, ok: Boolean, statusText: String, url: String, json: () => Promise<T>, text: () => Promise<String>, headers: {get: (String) => String}}> */
const fetch;
