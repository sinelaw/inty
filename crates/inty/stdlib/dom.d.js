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
//
// `Element<T>` and `Node<T>` below are the reusable forms of the inline
// row that `getElementById` / `createElement` / `querySelector` etc.
// produce. The `<T>` parameter is the "Element-like return type" for
// methods that hand back another element (`closest`, `cloneNode`,
// `appendChild`, `parentElement`, …). Users who annotate
// `function f(elt: Element<a>) => ...` get the same chaining behaviour
// the inline row supports, without spelling out the ~70-field row at
// every annotation site. `Node<T>` is the same shape minus the methods
// htmx-class code only ever calls on Element-shaped values; provided
// for completeness so non-Element nodes (text, comments, fragments)
// can be annotated narrowly.

// DOM events. There are no overloads keyed by the event name, so every
// listener gets one event shape, `DomEvent<T>`: the fields of the
// pointer, mouse, wheel, keyboard, input, focus, touch, drag and
// clipboard events together, the way every element here has one shape.
// A field the event at hand doesn't have reads as `undefined` at
// runtime (`e.key` of a pointer event), so read the fields the event
// you listen for has. `T` is the element-like type of `target`,
// `currentTarget` and `relatedTarget`. `PointerEvent<T>`,
// `KeyboardEvent<T>`, … name the same shape, to say which fields a
// handler means to read.

/** type DataTransfer = {
    dropEffect: String, effectAllowed: String, types: String[],
    files: {length: Int, item: (Int) => {name: String, size: Number, type: String, lastModified: Number, text: () => Promise<String>} | Null},
    getData: (String) => String, setData: (String, String) => Undefined,
    clearData: () => Undefined
} */

/** type Touch<T> = {
    identifier: Int, target: T, clientX: Number, clientY: Number,
    pageX: Number, pageY: Number, screenX: Number, screenY: Number,
    radiusX: Number, radiusY: Number, force: Number
} */

/** type DomEvent<T> = {
    type: String, target: T, currentTarget: T, bubbles: Boolean, cancelable: Boolean,
    defaultPrevented: Boolean, isTrusted: Boolean, timeStamp: Number,
    preventDefault: () => Undefined, stopPropagation: () => Undefined,
    stopImmediatePropagation: () => Undefined,
    clientX: Number, clientY: Number, pageX: Number, pageY: Number,
    screenX: Number, screenY: Number, offsetX: Number, offsetY: Number,
    movementX: Number, movementY: Number, x: Number, y: Number,
    button: Int, buttons: Int, relatedTarget: T | Null,
    pointerId: Int, pointerType: String, pressure: Number, width: Number, height: Number,
    isPrimary: Boolean,
    deltaX: Number, deltaY: Number, deltaZ: Number, deltaMode: Int,
    key: String, code: String, repeat: Boolean, isComposing: Boolean,
    shiftKey: Boolean, ctrlKey: Boolean, metaKey: Boolean, altKey: Boolean,
    getModifierState: (String) => Boolean,
    data: String | Null, inputType: String,
    touches: Touch<T>[], targetTouches: Touch<T>[], changedTouches: Touch<T>[],
    dataTransfer: DataTransfer | Null, clipboardData: DataTransfer | Null
} */

/** type Event<T> = DomEvent<T> */
/** type UIEvent<T> = DomEvent<T> */
/** type MouseEvent<T> = DomEvent<T> */
/** type PointerEvent<T> = DomEvent<T> */
/** type WheelEvent<T> = DomEvent<T> */
/** type KeyboardEvent<T> = DomEvent<T> */
/** type InputEvent<T> = DomEvent<T> */
/** type FocusEvent<T> = DomEvent<T> */
/** type TouchEvent<T> = DomEvent<T> */
/** type DragEvent<T> = DomEvent<T> */
/** type ClipboardEvent<T> = DomEvent<T> */

// Canvas 2D (`canvas.getContext("2d")`). A style is a CSS colour or a
// gradient.
/** type CanvasGradient = {addColorStop: (Number, String) => Undefined} */
/** type CanvasRenderingContext2D<T> = {
    canvas: T,
    fillStyle: String | CanvasGradient, strokeStyle: String | CanvasGradient,
    lineWidth: Number, lineCap: String,
    lineJoin: String, font: String, textAlign: String, textBaseline: String,
    globalAlpha: Number, globalCompositeOperation: String, imageSmoothingEnabled: Boolean,
    shadowBlur: Number, shadowColor: String, shadowOffsetX: Number, shadowOffsetY: Number,
    beginPath: () => Undefined, closePath: () => Undefined,
    moveTo: (Number, Number) => Undefined, lineTo: (Number, Number) => Undefined,
    rect: (Number, Number, Number, Number) => Undefined,
    roundRect: (Number, Number, Number, Number, Number) => Undefined,
    arc: (x: Number, y: Number, r: Number, start: Number, end: Number, ccw?: Boolean) => Undefined,
    arcTo: (Number, Number, Number, Number, Number) => Undefined,
    quadraticCurveTo: (Number, Number, Number, Number) => Undefined,
    bezierCurveTo: (Number, Number, Number, Number, Number, Number) => Undefined,
    ellipse: (Number, Number, Number, Number, Number, Number, Number) => Undefined,
    fill: () => Undefined, stroke: () => Undefined, clip: () => Undefined,
    fillRect: (Number, Number, Number, Number) => Undefined,
    strokeRect: (Number, Number, Number, Number) => Undefined,
    clearRect: (Number, Number, Number, Number) => Undefined,
    fillText: (text: String, x: Number, y: Number, maxWidth?: Number) => Undefined,
    strokeText: (text: String, x: Number, y: Number, maxWidth?: Number) => Undefined,
    measureText: (String) => {width: Number, actualBoundingBoxAscent: Number, actualBoundingBoxDescent: Number},
    save: () => Undefined, restore: () => Undefined,
    translate: (Number, Number) => Undefined, rotate: (Number) => Undefined,
    scale: (Number, Number) => Undefined,
    setTransform: (Number, Number, Number, Number, Number, Number) => Undefined,
    resetTransform: () => Undefined,
    setLineDash: (Number[]) => Undefined,
    createLinearGradient: (Number, Number, Number, Number) => CanvasGradient,
    createRadialGradient: (Number, Number, Number, Number, Number, Number) => CanvasGradient,
    drawImage: (image: T, dx: Number, dy: Number, dw?: Number, dh?: Number) => Undefined,
    getImageData: (Number, Number, Number, Number) => {width: Int, height: Int, data: Uint8Array},
    putImageData: ({width: Int, height: Int, data: Uint8Array}, Number, Number) => Undefined
} */

/** type Element<T> = {
    value: String, textContent: String, innerHTML: String, outerHTML: String,
    className: String, id: String, hidden: Boolean, disabled: Boolean,
    checked: Boolean, autofocus: Boolean, loading: String, tabIndex: Number,
    offsetWidth: Number, offsetHeight: Number, offsetTop: Number, offsetLeft: Number,
    scrollWidth: Number, scrollHeight: Number, scrollTop: Number, scrollLeft: Number,
    clientWidth: Number, clientHeight: Number, nodeName: String, tagName: String,
    onclick: (DomEvent<T>) => Undefined, oninput: (DomEvent<T>) => Undefined, onchange: (DomEvent<T>) => Undefined,
    onkeydown: (DomEvent<T>) => Undefined, onkeyup: (DomEvent<T>) => Undefined,
    onsubmit: (DomEvent<T>) => Undefined, onload: (DomEvent<T>) => Undefined,
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
    addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
    removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
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
    form: T,
    getRootNode: ({composed: Boolean}) => T,
    compareDocumentPosition: (T) => Number,
    async: Boolean,
    nonce: String,
    src: String,
    defer: Boolean
    ,
    width: Number, height: Number,
    getContext: (String) => CanvasRenderingContext2D<T>,
    toDataURL: () => String,
    setPointerCapture: (Int) => Undefined, releasePointerCapture: (Int) => Undefined,
    hasPointerCapture: (Int) => Boolean,
    dataset: {},
    scrollBy: (Number, Number) => Undefined, scrollTo: (Number, Number) => Undefined,
    select: () => Undefined,
    selectionStart: Int, selectionEnd: Int,
    files: {length: Int, item: (Int) => {name: String, size: Number, type: String, lastModified: Number, text: () => Promise<String>} | Null},
    play: () => Promise<Undefined>, pause: () => Undefined, currentTime: Number, paused: Boolean,
    title: String, placeholder: String, type: String, name: String, href: String,
    draggable: Boolean, contentEditable: String
} */

/** type Node<T> = {
    nodeName: String, textContent: String,
    parentElement: T, parentNode: T,
    appendChild: (T) => T, removeChild: (T) => T,
    insertBefore: (T, T) => T, replaceChild: (T, T) => T,
    cloneNode: (Boolean) => T,
    contains: (T) => Boolean,
    addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
    removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
    dispatchEvent: (T) => Boolean
} */

/** const document: <T>{
        getElementById: (String) => Element<T>,
        createElement: (String) => Element<T>,
        createDocumentFragment: () => T,
        querySelector: (String) => T,
        querySelectorAll: (String) => T[],
        addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
        removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
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
        visualViewport: {width: Number, height: Number, offsetLeft: Number, offsetTop: Number, pageLeft: Number, pageTop: Number, scale: Number, addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined, removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined},
        addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
        removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
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
            getItem: (String) => String | Null,
            setItem: (String, String) => Undefined,
            removeItem: (String) => Undefined,
            clear: () => Undefined,
            key: (Number) => String,
            length: Number
        },
        localStorage: {
            getItem: (String) => String | Null,
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
        prompt: (message: String, default?: String) => String | Null,
        matchMedia: (String) => {matches: Boolean, addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined},
        onpopstate: (T) => Undefined,
        origin: String
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
        clearAppBadge: () => Promise<Undefined>,
        mediaDevices: {
            getUserMedia: (constraints: {audio?: Boolean, video?: Boolean}) => Promise<MediaStream>
        }
    } */
const navigator;

// Types shared by the declarations below.

/** type Blob = {
    size: Number, type: String,
    slice: (start?: Int, end?: Int, type?: String) => Blob,
    text: () => Promise<String>, arrayBuffer: () => Promise<ArrayBuffer>
} */

/** type Response<T> = {
    status: Int, ok: Boolean, statusText: String, url: String, redirected: Boolean,
    json: () => Promise<T>, text: () => Promise<String>,
    arrayBuffer: () => Promise<ArrayBuffer>, blob: () => Promise<Blob>,
    headers: {get: (String) => String | Null, has: (String) => Boolean}
} */

/** type MediaStreamTrack = {kind: String, label: String, enabled: Boolean, stop: () => Undefined} */
/** type MediaStream = {
    id: String, active: Boolean,
    getTracks: () => MediaStreamTrack[], getAudioTracks: () => MediaStreamTrack[],
    getVideoTracks: () => MediaStreamTrack[]
} */

// A message channel's end (a worker's, an `AudioWorkletNode`'s `port`):
// every message on it is an `M`.
/** type MessagePort<M> = {
    postMessage: (message: M, transfer?: ArrayBuffer[]) => Undefined,
    onmessage: ({data: M}) => Undefined,
    start: () => Undefined, close: () => Undefined
} */

// WebSocket. A message's `data` is a string for a text frame and an
// `ArrayBuffer` for a binary one (with `binaryType = "arraybuffer"`):
// narrow it with `typeof e.data === "string"`.
/** type WebSocketMessage = {data: String | ArrayBuffer, type: String} */
/** const WebSocket: (url: String, protocols?: String) => {
        url: String, readyState: Int, bufferedAmount: Int, binaryType: String,
        protocol: String,
        send: (data: String | ArrayBuffer | Uint8Array | Float32Array) => Undefined,
        close: (code?: Int, reason?: String) => Undefined,
        onopen: ({type: String}) => Undefined,
        onclose: ({code: Int, reason: String, wasClean: Boolean}) => Undefined,
        onerror: ({type: String}) => Undefined,
        onmessage: (WebSocketMessage) => Undefined,
        addEventListener: (String, (WebSocketMessage) => Undefined) => Undefined,
        CONNECTING: Int, OPEN: Int, CLOSING: Int, CLOSED: Int
    } */
const WebSocket;

// ResizeObserver: the callback gets one entry per observed element that
// changed size.
/** const ResizeObserver: <T>((entries: {target: T, contentRect: {x: Number, y: Number, width: Number, height: Number, top: Number, left: Number, right: Number, bottom: Number}}[]) => Undefined) => {
        observe: (T) => Undefined,
        unobserve: (T) => Undefined,
        disconnect: () => Undefined
    } */
const ResizeObserver;

// Web Audio. As with elements, every node has one shape (`AudioNode<M>`,
// `M` the messages of an `AudioWorkletNode`'s port): the fields of the
// gain, analyser, buffer-source, oscillator and worklet nodes together.
/** type AudioParam = {
    value: Number, defaultValue: Number,
    setValueAtTime: (value: Number, time: Number) => Undefined,
    linearRampToValueAtTime: (value: Number, time: Number) => Undefined,
    exponentialRampToValueAtTime: (value: Number, time: Number) => Undefined,
    setTargetAtTime: (target: Number, time: Number, timeConstant: Number) => Undefined,
    cancelScheduledValues: (time: Number) => Undefined
} */
/** type AudioBuffer = {
    sampleRate: Number, length: Int, duration: Number, numberOfChannels: Int,
    getChannelData: (Int) => Float32Array,
    copyToChannel: (source: Float32Array, channel: Int, offset?: Int) => Undefined,
    copyFromChannel: (target: Float32Array, channel: Int, offset?: Int) => Undefined
} */
/** type AudioNode<M> = {
    numberOfInputs: Int, numberOfOutputs: Int, channelCount: Int,
    connect: (destination: AudioNode<M>, output?: Int, input?: Int) => AudioNode<M>,
    disconnect: () => Undefined,
    gain: AudioParam, frequency: AudioParam, detune: AudioParam, playbackRate: AudioParam,
    type: String,
    fftSize: Int, frequencyBinCount: Int, smoothingTimeConstant: Number,
    getFloatTimeDomainData: (Float32Array) => Undefined,
    getFloatFrequencyData: (Float32Array) => Undefined,
    getByteTimeDomainData: (Uint8Array) => Undefined,
    getByteFrequencyData: (Uint8Array) => Undefined,
    buffer: AudioBuffer | Null, loop: Boolean,
    start: (when?: Number, offset?: Number, duration?: Number) => Undefined,
    stop: (when?: Number) => Undefined,
    onended: () => Undefined,
    port: MessagePort<M>,
    parameters: {get: (String) => AudioParam | Undefined}
} */
/** type AudioContext<M> = {
    sampleRate: Number, currentTime: Number, state: String, baseLatency: Number,
    destination: AudioNode<M>,
    resume: () => Promise<Undefined>, suspend: () => Promise<Undefined>,
    close: () => Promise<Undefined>,
    createGain: () => AudioNode<M>, createAnalyser: () => AudioNode<M>,
    createBufferSource: () => AudioNode<M>, createOscillator: () => AudioNode<M>,
    createMediaStreamSource: (MediaStream) => AudioNode<M>,
    createBuffer: (channels: Int, length: Int, sampleRate: Number) => AudioBuffer,
    decodeAudioData: (ArrayBuffer) => Promise<AudioBuffer>,
    audioWorklet: {addModule: (String) => Promise<Undefined>}
} */
/** const AudioContext: <M>(options?: {sampleRate?: Number, latencyHint?: String}) => AudioContext<M> */
const AudioContext;
/** const AudioWorkletNode: <M, P>(context: AudioContext<M>, name: String, options?: {
        numberOfInputs?: Int, numberOfOutputs?: Int, outputChannelCount?: Int[],
        processorOptions?: P
    }) => AudioNode<M> */
const AudioWorkletNode;

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
// `fetch(url, init?)`; the request body is whatever the program sends
// (`B`: a string, a `Blob`, `FormData`, …).
/** const fetch: <T, B>(input: String, init?: {method?: String, headers?: Dict<String>, body?: B}) => Promise<Response<T>> */
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
// shape; both store String → String. A missing key reads as `null`.
/** const sessionStorage: {
        getItem: (String) => String | Null,
        setItem: (String, String) => Undefined,
        removeItem: (String) => Undefined,
        clear: () => Undefined,
        key: (Number) => String,
        length: Number
    } */
const sessionStorage;

/** const localStorage: {
        getItem: (String) => String | Null,
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
// `URL` per the WHATWG URL spec. Accepts an optional second `base`
// argument used to resolve a relative URL against an absolute one;
// htmx's `normalizePath` uses both 1-arg and 2-arg forms.
/** const URL: <T>{(url: String, base?: String) => {
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
    },
    createObjectURL: (T) => String,
    revokeObjectURL: (String) => Undefined
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
        addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
        removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
        readyState: Number,
        status: Number,
        statusText: String,
        response: T,
        responseText: String,
        responseType: String,
        responseURL: String,
        responseXML: T,
        upload: {
            addEventListener: (String, (DomEvent<T>) => Undefined) => Undefined,
            removeEventListener: (String, (DomEvent<T>) => Undefined) => Undefined
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
/** const Blob: <T>(parts: T[], options?: {type?: String}) => Blob */
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

// `Node` is used both as an `instanceof` operand and as a holder for
// the document-position constants (`Node.DOCUMENT_POSITION_PRECEDING`
// etc.) that `compareDocumentPosition` returns. Carry the constants
// here so `node.compareDocumentPosition(other) === Node.DOCUMENT_POSITION_*`
// expressions type-check. Values are the actual bit positions per
// DOM Living Standard §4.4.
/** const Node: {
        ELEMENT_NODE: Number,
        TEXT_NODE: Number,
        COMMENT_NODE: Number,
        DOCUMENT_NODE: Number,
        DOCUMENT_FRAGMENT_NODE: Number,
        DOCUMENT_POSITION_DISCONNECTED: Number,
        DOCUMENT_POSITION_PRECEDING: Number,
        DOCUMENT_POSITION_FOLLOWING: Number,
        DOCUMENT_POSITION_CONTAINS: Number,
        DOCUMENT_POSITION_CONTAINED_BY: Number,
        DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC: Number
    } */
const Node;

// `Document` carries the modern static `parseHTMLUnsafe` factory
// (HTML Living Standard, 2024+) in addition to its instanceof use.
// The return type is opaque (T) since the produced Document carries
// the same row shape as `document` but inty can't yet express that
// shared identity without recursion; users get back a row variable
// they can chain methods on via row polymorphism.
/** const Document: <T>{
        parseHTMLUnsafe: (String) => T
    } */
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
