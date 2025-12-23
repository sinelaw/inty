// Public-surface barrel module. Re-exports curated subsets of
// `lib-internal.js` under three different shapes:
//
//   - export { … } from "…"     — pick specific names, with renaming
//   - export * from "…"         — re-export every named export (skips default)
//   - export * as ns from "…"   — bundle the target's namespace under a name
//
// `app-reexport.js` imports through this barrel; nothing in
// `lib-internal.js` is reachable except via what we re-export here.

// Pick two names; rename one so callers see `triple` as `triplicate`.
export { double, triple as triplicate } from "./lib-internal.js";

// Re-export the target's default as our own default. Importers can write
// `import lib from "./lib.js";` and get `describe`.
export { default } from "./lib-internal.js";

// And give callers a way to reach the whole internal namespace explicitly.
export * as internals from "./lib-internal.js";
