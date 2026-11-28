// inty stdlib: a dedicated worker's global scope — the globals of the
// script a `new Worker(url)` runs (dom.d.js declares `Worker`). Not
// loaded by default (on a page's main thread `self` is the window); check
// such a script with `inty --lib builtin:worker`.
//
// The worker takes messages `I` and answers `O`, the reverse of the
// `Worker<I, O>` that runs it. `self` is declared for any `I` and `O`, so
// a handler stored into it would have to take every message type: name
// the scope with the worker's own message types once, and use that,
//
//     /** const scope: WorkerScope<ToWorker, FromWorker> */
//     const scope = self;
//     scope.onmessage = (e) => { scope.postMessage(answer(e.data), []); };
//
// (`self.postMessage(m)` alone, which stores nothing, needs no such name.)

/** type WorkerScope<I, O> = {
    onmessage: ({data: I}) => Undefined,
    onmessageerror: ({data: I}) => Undefined,
    postMessage: (message: O, transfer?: ArrayBuffer[]) => Undefined,
    close: () => Undefined,
    importScripts: (url: String) => Undefined,
    name: String
} */
/** const self: <I, O>WorkerScope<I, O> */
const self;

/** const postMessage: <O>(message: O, transfer?: ArrayBuffer[]) => Undefined */
const postMessage;

/** const importScripts: (url: String) => Undefined */
const importScripts;
