// Synthetic htmx-shape IIFE exercising JSDoc `@type {typeof helper}`
// declarations on public-API fields filled in after the object is built.
//
// The pattern (from bigskysoftware/htmx@master/src/htmx.js:5-69):
//
//     const htmx = {
//       /** @type {typeof onLoadHelper} */ onLoad: null,
//       /** @type {typeof processNode}   */ process: null,
//       ...30 more fields, all forward-referencing later helpers...
//     };
//     function onLoadHelper(...) { ... }
//     function processNode(...) { ... }
//     ...
//     htmx.onLoad = onLoadHelper;
//     htmx.process = processNode;
//
// A `null` initialiser is checked against the `@type` like any other
// (a field declared a function that is still `null` throws when
// called), so here the fields start as the hoisted helpers themselves
// and the late assignments re-fill them. `@type {typeof X}` types the
// public-API row at the helpers' function types, and downstream call
// sites type-check. (htmx's `null` fields would be declared
// `(typeof X) | Null`, and each call would test the field first.)

var lib = (function() {
  'use strict';

  const api = {
    /** @type {typeof onLoadHelper} */
    onLoad: onLoadHelper,
    /** @type {typeof processNode} */
    process: processNode,
    /** @type {typeof addClass} */
    addClass: addClass,
    /** @type {typeof removeClass} */
    removeClass: removeClass,
    /** @type {typeof triggerEvent} */
    trigger: triggerEvent,
    /** @type {typeof getConfig} */
    config: getConfig,

    // Bare-form `@type T` style (htmx's `config` properties use this).
    /**
     * @type Number
     * @default 0
     */
    requestCount: 0,
    /**
     * @type Boolean
     * @default true
     */
    historyEnabled: true,
    /**
     * @type String
     * @default 'innerHTML'
     */
    defaultSwapStyle: 'innerHTML',

    // No annotation: synthesised normally.
    version: '2.0.0',
  };

  function onLoadHelper(callback) {
    return callback;
  }
  function processNode(elt) {
    return elt;
  }
  function addClass(elt, cls) {
    return cls;
  }
  function removeClass(elt, cls) {
    return cls;
  }
  function triggerEvent(elt, name, detail) {
    return detail;
  }
  function getConfig() {
    return { ready: true };
  }

  // Late assignment — htmx fills these in just before returning. The
  // assignments type-check because the field types match the helper
  // functions' types via `@type {typeof helper}`.
  api.onLoad = onLoadHelper;
  api.process = processNode;
  api.addClass = addClass;
  api.removeClass = removeClass;
  api.trigger = triggerEvent;
  api.config = getConfig;

  return api;
})();

// Public-API call sites: each typed by the @type annotation on the
// corresponding field.
var x = lib.process(42);
var s = lib.addClass(0, "active");
var detail = lib.trigger(0, "click", { x: 1, y: 2 });
var cfg = lib.config();
var ready = cfg.ready;

// The bare-form fields are accessible as their declared types.
var count = lib.requestCount + 1;
var historyOn = lib.historyEnabled && true;
var style = lib.defaultSwapStyle.length;
