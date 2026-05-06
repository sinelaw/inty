# Running inty on Basecamp's fizzy

A real-world stress-test of the inty subset against a current Hotwired/Stimulus
Rails app: [`basecamp/fizzy`](https://github.com/basecamp/fizzy), `app/javascript/`.

* 87 JS files, 4 114 LOC
* 65 controllers, 9 helpers, 5 initializers, 2 webauthn libs, 6 native-bridge controllers
* Heavy Stimulus, importmap-rails, web components, async DOM, WebAuthn

Reproduction:

```sh
git clone --depth=1 https://github.com/basecamp/fizzy.git /tmp/fizzy
cargo build --release -p inty-cli
cd /tmp/fizzy/app/javascript
for f in $(find . -name '*.js'); do
  /path/to/inty --no-color "$f" > /dev/null 2>&1 || echo "FAIL: $f"
done
```

Result: **0 / 87 files type-check.** Every file errors out at the parser or the
type checker before the existing-stdlib limit ever gets exercised.

## First-error histogram

```
48  Unexpected character: '#'                       (private class fields/methods)
22  Unexpected token: found 'class', expected expr  (export default class extends X)
 6  cannot resolve import '@hotwired/...'           (importmap bare specifiers)
 3  Unexpected token: found 'async'                 (export async function)
 3  Unexpected token: found '=', expected ) | }     (default params, destructuring defaults)
 2  Unexpected character / wrong stdlib type        (Element shape, navigator, Date)
 1  Unexpected token: found '}'                     (orientation_helpers, destructuring default in nested pattern)
 ...                                                (long tail in stdlib coverage)
```

The histogram only counts **first** errors; the actual surface of unsupported
constructs is wider per file.

## Categorized gaps

Counts are file-level (87 total).

### A. By-design "out of scope" in `examples/spa/gaps.md`

| Gap                                | Files | Notes                                                                     |
|------------------------------------|-------|---------------------------------------------------------------------------|
| `extends Controller` / inheritance | 68    | Every Stimulus controller and `class PasskeyButton extends HTMLElement`   |
| Private class fields (`#x`)        | 39    | `#timer`, `#perform`, `get #dirty`, `#extractContentFromMetaTag`          |
| `static` class members             | 48    | `static targets`, `static values`, `static classes`, `static outlets`     |
| `super.method()`                   | 7     | All bridge controllers call `super.connectedCallback()` etc.              |

These are flagged as deliberately rejected in `examples/spa/gaps.md` ("By design:
prototype chain and anything that rides on it"). Stimulus is essentially the
poster child for everything in that section.

### B. Parser-level gaps that aren't fundamentally about the type system

| Construct                               | Example                              | Where                          |
|-----------------------------------------|--------------------------------------|--------------------------------|
| `export async function f(){...}`        | `export async function submitForm…`  | helpers/form_helpers.js, helpers/scroll_helpers.js, lib/action_pack/webauthn.js |
| `export default class extends X {...}`  | every controller                     | 68 files                       |
| Default parameter values                | `function throttle(fn, delay = 1000)`| helpers/timing_helpers.js, helpers/text_helpers.js, lib/action_pack/* |
| Destructuring defaults                  | `function orient({ target, anchor = null, reset = false })` | helpers/orientation_helpers.js |
| Rest parameters                         | `function f(...args)`                | helpers/timing_helpers.js etc. |
| Spread in call arguments                | `String.fromCharCode(...bytes)`, `Math.max(...arr)` | lib/action_pack/webauthn.js   |
| `try { ... } catch {}` (no binding)     | `await navigator.clipboard.writeText(...) ; ... } catch {}` | controllers/copy_to_clipboard_controller.js |
| Class field with arrow initializer      | `#perform = async () => { ... }`     | lib/action_pack/passkey.js     |
| Tagged template literal                 | `` String.raw`hi` ``                  | (probed, not present in fizzy) |

All seven are pure parser additions. Items 1–5 in particular are listed in the
README's "Future Work" or in `examples/spa/gaps.md` § destructuring/round-2,
but aren't done.

### C. Module-resolution gaps

Fizzy uses Rails importmap, so most imports look like:

```js
import { Controller } from "@hotwired/stimulus"        // bare package
import { application } from "controllers/application"  // unprefixed app path
import "initializers"                                  // directory-as-module
```

inty's resolver only handles relative paths (`./foo.js`, `../bar.js`).
The bundler crate already documents that bare specifiers are rejected.
Supporting fizzy would need at minimum:

* A path-alias / `paths` config layer (tsconfig-paths style) so the Rails
  `app/javascript/` root can be the import root.
* A way to declare-only stub `node_modules`-ish packages (`@hotwired/stimulus`,
  `@rails/request.js`, etc.) for inty to consume their `.d.js`.

### D. Stdlib / declaration-set gaps

The shipped `stdlib/dom.d.js` is intentionally minimal: Element has 11 fields
and Document has 4 methods. Fizzy reaches well past that, even in the helpers.

Missing globals (referenced by ≥ 1 file each):

* `Date` (constructor + methods) — `helpers/date_helpers.js` is unrunnable
  without it.
* `navigator` (`navigator.maxTouchPoints`, `.clipboard.writeText`,
  `.setAppBadge`, `.clearAppBadge`, `.credentials.create`, `.credentials.get`)
  — `helpers/platform_helpers.js`, `controllers/badge_controller.js`,
  `controllers/copy_to_clipboard_controller.js`, `lib/action_pack/webauthn.js`.
* `URLSearchParams`, `FormData`, `AbortController`, `TextDecoder`, `Uint8Array`,
  `CustomEvent`, `customElements`, `atob`, `btoa` — `lib/action_pack/*`.
* `window.visualViewport`, `window.scrollX/Y`, `window.location` (mutation),
  `window.PublicKeyCredential`, mutation of `window.Stimulus`, `window.Current`.

Missing or thin Element/Document API:

* `setAttribute`, `getAttribute`, `addEventListener`, `removeEventListener`,
  `querySelector`, `querySelectorAll`, `dispatchEvent`, `closest`, `contains`,
  `cloneNode`, `before`, `remove`, `focus`, `blur`, `submit`, `requestSubmit`,
  `getBoundingClientRect`, `scrollTop` / `scrollLeft`, `offsetWidth`,
  `dataset.*`, `classList.{add,remove,toggle,contains}`, `hidden`, `loading`,
  `autofocus`, `disabled`.
* The current `getElementById`/`createElement` return *the same flat row* with
  fixed event handlers and no `setAttribute`. As soon as a file calls anything
  outside that row, inty rejects it.

Missing static methods on builtins:

* `String.fromCharCode`, `String.raw`.
* `Date.now`, `new Date(seconds)`, `new Date(y, m, d)`.
* `Object.assign`, `Object.entries`, `Object.values`, `Object.fromEntries`.
* `Array.from` (used in `Array.from(...).forEach(...)` in dialog_controller).

### E. Real bugs in inty (not just open gaps)

#### `export function` does not hoist.

`gaps.md` § 1 says hoisting was resolved, but it only covers plain `function`
declarations. With `export`, peer references break:

```js
// helpers/date_helpers.js
export function differenceInDays(fromDate, toDate) {
  return Math.round(Math.abs((beginningOfDay(toDate) - beginningOfDay(fromDate)) / 86400000))
}
export function beginningOfDay(date) { return new Date(...) }
```

```
Error: Undefined variable: 'beginningOfDay'
```

Minimal repro:

```js
export function a(x) { return b(x); }
export function b(x) { return 1; }
```

Plain `function a/b` works; `export function a/b` does not. The
`infer_stmt_list` two-pass binding-group code presumably runs before the
export collector has registered the names, or the export wrapper isn't part
of the same hoisting group.

#### `delete o.a` types as `Boolean` but leaves `o`'s row unchanged.

```js
var o = {a: 1, b: 2};
delete o.a;
// o still types as {a: Number, b: Number}; subsequent o.a reads pass.
```

Silent unsoundness, low priority because rare in practice.

### F. Type-system gaps that bite Stimulus specifically

**Stimulus dynamic property generation.** A controller with

```js
static targets = ["unread"]
static values  = { limit: Number, count: Number }
static classes = ["unread"]
```

acquires, at runtime: `this.unreadTarget`, `this.unreadTargets`,
`this.hasUnreadTarget`, `this.limitValue`, `this.hasLimitValue`,
`this.limitValueChanged()`, `this.unreadClass`, `this.hasUnreadClass`, etc.
Forty of fizzy's controllers (out of 65) use these.

This is several steps past row-poly: the instance shape is keyed on a
class-static literal. Even after inheritance and `static` were added to inty,
typing Stimulus would need either (a) TS-mapped-types-style derivation from
the static literal or (b) an out-of-band `.d.js` per controller.

**Nullable / optional property types.** Already gap §3. Bites
`document.head.querySelector(...)?.getAttribute("content")`, the WebAuthn
`navigator.credentials.create()` return shape, every `?.` on a possibly
nullable receiver, and `Current.user` (returns `{id}` or implicitly
`undefined`).

## Effective coverage with realistic short-term work

If the **B** (parser) and **D** (stdlib) gaps were closed but the **A**
(by-design) and **F** (Stimulus dynamic props) ones stayed, inty would type
roughly:

| Directory                    | Files | LOC  | Reachable after parser+stdlib? |
|------------------------------|-------|------|--------------------------------|
| `controllers/**`             | 68    | 3 290 | No — every file is `class … extends Controller` |
| `helpers/**`                 | 9     | 232  | Mostly yes (forward-ref bug aside) |
| `initializers/**`            | 5     | 31   | Partial — `current.js` has a class & private method |
| `lib/action_pack/**`         | 2     | 261  | No — `extends HTMLElement`, private class fields, `super.…`, class arrow-fields |

So roughly **~6 % of LOC** becomes reachable, and the architectural blocker is
the `class … extends X` requirement of every Stimulus controller.

## What JavaScript changes would fizzy need?

To make fizzy type-check under inty as it stands today, every Stimulus
controller would need to be rewritten as a factory function returning a row,
losing Stimulus auto-wiring entirely. That isn't really "JavaScript changes" —
it's "stop using Stimulus." Concretely:

1. Replace `export default class extends Controller { ... }` with
   `export default function setup(element) { … return { connect, disconnect, … } }`.
2. Replace private-field state with closure-captured `let`s.
3. Replace `static targets/values/classes/outlets` with a manual
   `element.querySelector("[data-foo-target]")` etc. at the top of `setup()`.
4. Replace `extends HTMLElement` (passkey.js) with the same row-factory
   pattern; lose the `connectedCallback` / `disconnectedCallback` lifecycle
   hooks — `customElements.define` requires a class.
5. Replace default params with explicit `if (x === undefined) x = …`.
6. Replace `...rest` and `...spread` in calls / params with explicit array
   construction or `.apply`.
7. Drop `try { } catch {}` for `try { } catch (_) {}`.
8. Add explicit `null` widening where `?.` is used today.

Even after all that, fizzy still uses ~30 browser APIs not in `stdlib/dom.d.js`,
so inty's stdlib has to grow before any of it type-checks.

## Suggested priority order for inty

In rough order of "biggest unblock per unit of work":

1. **Parser**: default params, destructuring defaults, rest/spread params,
   spread in calls, `export async function`, `catch {}` without binding,
   `export default class …`, class arrow-field initializers. Most are
   single-token / single-arm fixes.
2. **Bug fix**: `export function` hoisting (peer forward references).
3. **Stdlib**: `Date`, `navigator.{clipboard,credentials,maxTouchPoints,…}`,
   common DOM Element methods (`addEventListener`, `querySelector*`, `setAttribute`,
   `classList.*`, `dataset`, `closest`, `getBoundingClientRect`),
   `URLSearchParams`, `FormData`, `AbortController`, `TextDecoder`, `Uint8Array`,
   `CustomEvent`, `customElements`, `atob`/`btoa`, `Regex` methods (`test`,
   `match`, `exec`), `Array.from`, `Object.assign/entries/values`,
   `String.fromCharCode`, `String.raw`.
4. **Module resolver**: path aliases (importmap-style or tsconfig-paths-style)
   and stub-package resolution. Lets inty *see* `@hotwired/stimulus` etc. as
   declaration files even before the underlying class model exists.
5. **Type-system**: nullable/option types (already top of gaps.md "what's left"),
   then revisit "by design" items only if there is appetite for nominal class
   types and inheritance — the only path to typing Stimulus controllers as
   themselves.

Items 1–4 are scoped enough to do incrementally; item 5 is a strategic
decision that the "by design" section of `gaps.md` currently rules out.
