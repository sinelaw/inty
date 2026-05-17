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
        setTimeout: (() => Undefined, Number) => Number,
        setInterval: (() => Undefined, Number) => Number,
        clearTimeout: (Number) => Undefined,
        clearInterval: (Number) => Undefined,
        history: {
            length: Number,
            state: T,
            scrollRestoration: String,
            back: () => Undefined,
            forward: () => Undefined,
            go: (Number) => Undefined,
            pushState: (T, String, String) => Undefined,
            replaceState: (T, String, String) => Undefined
        },
        sessionStorage: {
            getItem: (String) => String,
            setItem: (String, String) => Undefined,
            removeItem: (String) => Undefined,
            clear: () => Undefined,
            key: (Number) => String,
            length: Number
        },
        localStorage: {
            getItem: (String) => String,
            setItem: (String, String) => Undefined,
            removeItem: (String) => Undefined,
            clear: () => Undefined,
            key: (Number) => String,
            length: Number
        },
        navigator: {userAgent: String, language: String, platform: String, vendor: String, onLine: Boolean},
        document: T,
        atob: (String) => String,
        btoa: (String) => String,
        fetch: (String) => Promise<{status: Number, ok: Boolean, statusText: String, url: String, json: () => Promise<T>, text: () => Promise<String>}>,
        alert: (String) => Undefined,
        confirm: (String) => Boolean,
        prompt: (String) => String,
        matchMedia: (String) => {matches: Boolean, addEventListener: (String, (T) => Undefined) => Undefined}
    } */
const window;

// History API as a top-level global. Mirrors `window.history`. inty
// has no module-level reference identity, so the two appear as
// separate row instantiations — fine for type-checking purposes.
/** const history: <T>{
        length: Number,
        state: T,
        scrollRestoration: String,
        back: () => Undefined,
        forward: () => Undefined,
        go: (Number) => Undefined,
        pushState: (T, String, String) => Undefined,
        replaceState: (T, String, String) => Undefined
    } */
const history;

// Reflect. A few htmx-class libraries use Reflect.has and Reflect.get
// for safer property access on user-supplied objects.
/** const Reflect: <T, V>{
        get: (T, String) => V,
        set: (T, String, V) => Boolean,
        has: (T, String) => Boolean,
        deleteProperty: (T, String) => Boolean,
        ownKeys: (T) => String[],
        getPrototypeOf: (T) => V,
        setPrototypeOf: (T, V) => Boolean
    } */
const Reflect;

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

// `window.location` and the bare `location` global are aliases for the
// same Location object. Setting `href` triggers navigation; the rest
// of the row exposes the parsed URL parts and the navigation methods.
/** const location: {
        href: String,
        protocol: String,
        host: String,
        hostname: String,
        port: String,
        pathname: String,
        search: String,
        hash: String,
        origin: String,
        assign: (String) => Undefined,
        replace: (String) => Undefined,
        reload: () => Undefined,
        toString: () => String
    } */
const location;

// Web Storage. `sessionStorage` and `localStorage` share the same
// shape; both store String → String. Real browsers return `null` for
// missing keys; inty collapses that to the same `String` slot.
/** const sessionStorage: {
        getItem: (String) => String,
        setItem: (String, String) => Undefined,
        removeItem: (String) => Undefined,
        clear: () => Undefined,
        key: (Number) => String,
        length: Number
    } */
const sessionStorage;

/** const localStorage: {
        getItem: (String) => String,
        setItem: (String, String) => Undefined,
        removeItem: (String) => Undefined,
        clear: () => Undefined,
        key: (Number) => String,
        length: Number
    } */
const localStorage;

// URL constructor. The (String) call form covers both `URL(href)` and
// `new URL(href)`. The two-argument `new URL(href, base)` form is out
// of scope under the unified callable-row design — callers compose
// the absolute href first.
/** const URL: (String) => {
        href: String,
        protocol: String,
        host: String,
        hostname: String,
        port: String,
        pathname: String,
        search: String,
        hash: String,
        origin: String,
        searchParams: {
            get: (String) => String,
            has: (String) => Boolean,
            set: (String, String) => Undefined,
            append: (String, String) => Undefined,
            delete: (String) => Undefined,
            toString: () => String
        },
        toString: () => String
    } */
const URL;

// XMLHttpRequest. The de-facto shape htmx uses; modern code prefers
// `fetch` but every framework needs to talk to legacy servers. Event
// listeners receive an opaque (T) since the event surface depends on
// the listener name. `response` and `responseXML` are also opaque (T)
// because they vary with `responseType`.
/** const XMLHttpRequest: <T>() => {
        open: (String, String) => Undefined,
        send: (T) => Undefined,
        setRequestHeader: (String, String) => Undefined,
        getResponseHeader: (String) => String,
        getAllResponseHeaders: () => String,
        overrideMimeType: (String) => Undefined,
        abort: () => Undefined,
        addEventListener: (String, (T) => Undefined) => Undefined,
        removeEventListener: (String, (T) => Undefined) => Undefined,
        readyState: Number,
        status: Number,
        statusText: String,
        response: T,
        responseText: String,
        responseType: String,
        responseURL: String,
        responseXML: T,
        upload: {
            addEventListener: (String, (T) => Undefined) => Undefined,
            removeEventListener: (String, (T) => Undefined) => Undefined
        },
        withCredentials: Boolean,
        timeout: Number,
        onload: () => Undefined,
        onerror: () => Undefined,
        ontimeout: () => Undefined,
        onabort: () => Undefined,
        onreadystatechange: () => Undefined
    } */
const XMLHttpRequest;

// IntersectionObserver. The callback receives an array of entries
// (opaque T because the entry row references the observed element).
/** const IntersectionObserver: <T>(((T[]) => Undefined), T) => {
        observe: (T) => Undefined,
        unobserve: (T) => Undefined,
        disconnect: () => Undefined,
        takeRecords: () => T[]
    } */
const IntersectionObserver;

// MutationObserver. Same shape as IntersectionObserver; second
// argument to observe() is the options row.
/** const MutationObserver: <T, O>(((T[]) => Undefined)) => {
        observe: (T, O) => Undefined,
        disconnect: () => Undefined,
        takeRecords: () => T[]
    } */
const MutationObserver;

// Blob. Binary data; first arg is the parts array, second the options
// row (`{type: String}`). Opaque T for the parts and result of
// arrayBuffer() since both can hold ArrayBuffer / Uint8Array etc.
/** const Blob: <T>(T[], T) => {
        size: Number,
        type: String,
        slice: (Number, Number, String) => {size: Number, type: String},
        text: () => Promise<String>,
        arrayBuffer: () => Promise<T>
    } */
const Blob;

// DOMParser. Returns whatever document-shaped value `T` resolves to
// at the call site; the htmx fragment-parsing path expects the
// existing Element row.
/** const DOMParser: <T>() => {
        parseFromString: (String, String) => T
    } */
const DOMParser;

// CSS namespace.
/** const CSS: {
        escape: (String) => String,
        supports: (String) => Boolean
    } */
const CSS;

// XPathEvaluator. htmx's hyperscript bridge uses this for advanced
// selectors. Opaque T for results because XPath can return nodes,
// strings, numbers, or booleans depending on the result type.
/** const XPathEvaluator: <T>() => {
        evaluate: (String, T, T, Number, T) => T,
        createExpression: (String, T) => {
            evaluate: (T, Number, T) => T
        }
    } */
const XPathEvaluator;

// DOM constructor sentinels. Used almost exclusively as the right-
// hand side of `instanceof` checks (`evt.target instanceof
// HTMLFormElement`). inty's `instanceof` returns Boolean for any
// pair of operands (operators/mod.rs:193), so an empty closed row
// satisfies the type checker without overcommitting to a constructor
// signature inty can't faithfully express (these aren't directly
// constructible with `new` in real browsers either). Narrowing the
// LHS to a more specific element type via `instanceof` is feature
// work beyond stdlib.
/** const Element: {} */
const Element;

/** const HTMLElement: {} */
const HTMLElement;

/** const HTMLFormElement: {} */
const HTMLFormElement;

/** const HTMLInputElement: {} */
const HTMLInputElement;

/** const HTMLSelectElement: {} */
const HTMLSelectElement;

/** const HTMLTextAreaElement: {} */
const HTMLTextAreaElement;

/** const HTMLButtonElement: {} */
const HTMLButtonElement;

/** const HTMLAnchorElement: {} */
const HTMLAnchorElement;

/** const HTMLImageElement: {} */
const HTMLImageElement;

/** const HTMLScriptElement: {} */
const HTMLScriptElement;

/** const HTMLTemplateElement: {} */
const HTMLTemplateElement;

/** const Node: {} */
const Node;

/** const Document: {} */
const Document;

/** const DocumentFragment: {} */
const DocumentFragment;

/** const ShadowRoot: {} */
const ShadowRoot;

/** const Text: {} */
const Text;

/** const Comment: {} */
const Comment;

/** const SVGElement: {} */
const SVGElement;
