# SCC-based binding inference

Design sketch for replacing inty's adjacent-function-decl hoisting with
dependency-driven strongly-connected-component (SCC) inference,
following the standard approach from the ML/Haskell lineage. The
motivation is gap 4 in [`crates/inty/tests/htmx_gaps.rs`](../crates/inty/tests/htmx_gaps.rs)
(the IIFE library pattern used by htmx, jQuery, lodash, Day.js, etc.).
Status: design only — no code yet.

The guiding principle is **match ECMAScript strict-mode semantics
exactly**. Every rule below is justified by what V8/JSC/SpiderMonkey
actually do when given the same source. We use *strict* mode because
ES modules are strict by default, htmx and friends open with
`'use strict'`, and Annex B "sloppy mode" function-in-block semantics
are an explicit web-compatibility hack that no new tooling should
emulate.

## What ECMAScript says about hoisting

ES § 14 (Declarations and the Variable Statement), § 16 (Scripts and
Modules), and § 9 (Executable Code and Execution Contexts) divide
declarations into three categories with different visibility rules.

| Form                       | Hoisted? | Value before init line | Use before init |
|----------------------------|----------|------------------------|-----------------|
| `function f() {…}` at top of function/script/module | Name **and** value hoisted to top of containing function/script/module | The function itself | OK — returns the function |
| `function f() {…}` inside a block (`if`, `for`, …) in strict mode | Name and value hoisted to top of the **block**, not the enclosing function | The function itself (within the block) | OK *within the block*; outside the block, `f` doesn't exist |
| `var x = e`                | Name hoisted to top of containing function/script/module | `undefined` | Reads `undefined`; calling `undefined()` is a TypeError |
| `let x = e` / `const x = e`| Lexically scoped to enclosing block | TDZ (does not exist) | **ReferenceError** |
| `class C {…}`              | Lexically scoped to enclosing block | TDZ            | **ReferenceError** |
| `var f = function() {…}`   | Same as `var x = e`: name hoisted, value `undefined` | `undefined` | Calling `f()` before the line throws TypeError |

The only declaration form that hoists *with its value* is
`function`/`export function`. That's the only form inty should treat
as hoistable.

The block-vs-function-scope distinction matters: in strict mode,
`function f` inside `if (cond) { … }` is **block-scoped**, not
hoisted up to the enclosing function. inty already mirrors this
because `Stmt::Block` recurses into `infer_stmt_list` with its own
fresh scope — the SCC pre-pass runs per `infer_stmt_list` call, so
block-scoped function decls stay confined to their block. No new
logic needed; we just preserve today's recursion structure.

## Problem recap

Today `infer_stmt_list` (in `src/infer/mod.rs`) walks statements
left-to-right and groups *contiguous* `function` declarations into a
binding group. `infer_function_group` does textbook let-rec inference
on each group: hoist names → infer all bodies → generalise. Any
non-function statement between two `function` decls breaks the group,
so a forward reference across the break fails with "Undefined
variable".

This rejects programs that ECMAScript accepts. For example, every
browser evaluates this without error:

```js
function a() { return b(); }
const sep = 1;
function b() { return 1; }
a(); // 1
```

inty rejects it because `a`'s body sees `b` as undefined — `b`'s
declaration is in a separate "group" after `const sep`. The htmx
source hits this on its first interesting line and never recovers.

The standard fix is dependency analysis: hoist *every* `function`
declaration in a scope (as ECMAScript does) before inferring any
body, then process mutually-recursive sub-groups (SCCs of the call
graph) in topological order.

## Target rule

In a scope with bindings B₁ … Bₙ in source order:

1. Pre-pass — collect every **hoistable** binding into a name map
   with a fresh monomorphic type variable. Hoistable = exactly the
   declaration forms that ECMAScript hoists with their value:
   `function f` and `export function f` declarations at the immediate
   statement-list level. `var`/`let`/`const` initialisers (including
   `var f = function…`), `class` declarations, and `function` decls
   nested inside `if`/`for`/`while`/`try`/etc. blocks all stay out
   of the hoistable set — they're not value-hoisted by ECMAScript
   either.
2. Compute a directed graph over the hoistable names where `f → g`
   iff `f`'s body free-references `g`. Compute SCCs (Tarjan's),
   topologically order them.
3. For each SCC in topo order, run the existing
   `infer_function_group` logic on its members: infer every body
   against the shared env (other-SCC members as already-generalised
   schemes, same-SCC members as monomorphic vars), unify, generalise
   all at the SCC boundary. The result extends the scope's env.
4. Walk the original statement list in source order. For every
   statement that *isn't* a hoistable function decl, infer it
   normally against the now-fully-populated env. For hoistable
   function decls, no-op — they're already typed.

Property we want: principal types per SCC (Hindley-Milner soundness
+ completeness for HM-restricted programs), and every JS program
whose static call graph forms an acyclic-after-SCC structure
type-checks regardless of source ordering — matching strict-mode
ECMAScript visibility exactly.

## What stays the same

- The body-inference primitive (`infer_function`) is unchanged.
- `infer_function_group` is reused per-SCC unmodified.
- The value restriction (`InferConfig`) stays where it is — it
  affects generalisation inside an SCC, orthogonal to which
  bindings are in the SCC.
- Recorded types/spans for the LSP path (`record_decl_type`,
  `record_decl_scheme`) keep their existing key.
- Non-function statements still flow in source order; their
  inference can call into the pre-populated function env (this
  matches JS hoisting semantics — function decls are visible from
  the top of the scope).
- Behaviour for any single-group, source-order program is
  unchanged (the SCC partition over `[f, g, h]` with no intervening
  decls produces one SCC, same as today's adjacent group).

## What changes

### Data structures

```rust
// in src/infer/features/functions.rs

/// One hoistable binding in a scope: a `function` or `export function`
/// declaration plus the AST it was lifted from, indexed by name.
struct Hoisted<'a> {
    name: &'a str,
    stmt: &'a Stmt,     // the original AST node, for span/parts extraction
    fresh_var: Type,    // monomorphic TVar assigned in the pre-pass
}

/// SCC analysis result. `order` is the topological order of SCCs;
/// each SCC is a list of indices into `bindings`.
struct SccPartition<'a> {
    bindings: Vec<Hoisted<'a>>,
    order: Vec<Vec<usize>>,    // outer Vec is topo order; inner Vec is one SCC
}
```

### New helper: free-identifier walker

We need a `free_identifiers(body: &Stmt) -> HashSet<String>` over the
AST. inty's existing `free_vars` is for type variables, not source
identifiers, so this is new. It's a pure-AST walk; ~80 lines.

The walker collects every `Expr::Ident { name, .. }` it sees, minus
names bound by inner scopes (function params, destructuring patterns,
nested `function`/`let`/`const`/`var` decls inside nested function
bodies — we follow JS lexical scoping). For the dependency analysis
we only care about names that appear in the *current* scope's
hoistable set, so we can intersect after collection.

This walker is also useful on its own (free-vars analysis for the LSP,
dead-code linting, …) — design point: put it in
`src/parser/free_idents.rs` next to the AST.

### `infer_stmt_list` two-pass shape

```rust
pub(crate) fn infer_stmt_list(
    &mut self,
    env: &TypeEnv,
    stmts: &[Stmt],
) -> InferResult<(Type, TypeEnv)> {
    // Pass 1 — collect hoistable function decls; assign fresh vars.
    let bindings = collect_hoistable_bindings(stmts);
    let mut env = env.clone();
    for h in &bindings {
        env = env.extend(h.name.to_string(), TypeScheme::mono(h.fresh_var.clone()));
    }

    // Pass 2 — dependency analysis + topo SCC inference.
    let partition = compute_scc_partition(&bindings);
    for scc in &partition.order {
        let group: Vec<&Stmt> = scc.iter().map(|i| bindings[*i].stmt).collect();
        env = self.infer_function_group_with_vars(&env, &group, &bindings, scc)?;
    }

    // Pass 3 — walk source order, infer non-function statements.
    // Same shape as today's loop; the `is_function_like_decl` arm
    // becomes a no-op (already typed in pass 2). Duplicate-`const`
    // tracking is unchanged.
    let mut result = Type::Undefined;
    let mut const_names = HashSet::new();
    for stmt in stmts {
        if is_function_like_decl(stmt) { continue; }
        check_dup_const(stmt, &mut const_names)?;
        let (ty, new_env) = self.infer_stmt(&env, stmt)?;
        result = ty;
        env = new_env;
    }
    Ok((result, env))
}
```

`infer_function_group_with_vars` is a small extension to today's
`infer_function_group`: it accepts the pre-computed fresh vars
(so the SCC analysis and the inference share one set of TVars
rather than re-hoisting). Could fold into a single function with
an optional pre-hoist argument.

### SCC algorithm

Tarjan's iterative variant — ~50 lines of pure Rust. Inputs are
the bindings vector and a callback that gives each binding's
referenced indices (intersection of free-identifier set with the
hoistable name map). We don't need any inty types to do this; it's
a graph algorithm over `usize` node ids.

## Rules pinned by ECMAScript (no design choices required)

Each item below is settled by what the spec says and what V8/JSC/
SpiderMonkey actually do; we just follow.

### 1. Scope boundaries — per `infer_stmt_list` call

ES § 9.2.10 (FunctionDeclarationInstantiation) hoists `function`
declarations to the top of the **VariableEnvironment** of the
enclosing function or script. For a block (`if`, `for`, `while`,
…) in strict mode, ES § 14.2 + § 14.4 introduce a separate
**LexicalEnvironment** for the block; function decls inside the
block are bound there, not in the enclosing function. The
behaviour, mirrored by every engine:

```js
'use strict';
function outer() {
  if (true) {
    function inner() { return 1; }
    inner();         // 1
  }
  return inner();    // ReferenceError: inner is not defined
}
```

inty already matches this for free: `Stmt::Block` recurses into
`infer_stmt_list` with a fresh inner scope, so the SCC pre-pass
runs per-block. Function decls inside an `if`/`for`/`while`
hoist to the immediate block, not to the surrounding function.
**No change to the existing recursion structure.**

### 2. `var f = function() {…}` is *not* hoistable

Per ES § 14.3.2 (VariableDeclaration) the binding is created at
function-entry with the value `undefined`; the function value is
only assigned when the assignment expression executes. Calling
`f()` before the line is a runtime `TypeError: f is not a function`
in every engine. Treating it as hoistable would type-check programs
that the spec says crash. Stay out of the hoistable set.

The same applies to `let f = function…` and `const f = function…`:
both are TDZ before the line. Not hoistable.

### 3. Class declarations

Per ES § 15.7.10, class declarations are lexically scoped and
TDZ before their declaration line. Engines throw
`ReferenceError: Cannot access 'C' before initialization`. Not
hoistable.

### 4. `function` declarations inside blocks (the Annex B trap)

ES Annex B.3.2 specifies the legacy web-compatibility semantics
that sloppy-mode browsers implement: a `function f` inside a block
gets *both* a block-scoped binding and a `var`-hoisted binding in
the enclosing function, with cross-update on assignment. This is
explicitly described in the spec as a hack for legacy code that
"no new code should rely on."

Strict-mode programs (every ES module, anything starting with
`'use strict'`) **do not** get Annex B; the function decl is
strictly block-scoped. inty assumes strict mode throughout
(consistent with treating ES modules as the default), so we
implement only the strict rule: function decls inside blocks
hoist to the block, never to the enclosing function.

### 5. TDZ diagnostics

For `let` / `const` / `class`, ES specifies a `ReferenceError`
on any access before the declaration line is reached. inty's
current "Undefined variable" error catches the static cases
because these forms aren't in the hoistable set — they're
processed in source order, and a reference before the decl
hits an env that doesn't contain the name yet. The SCC change
preserves this exactly: only `function` decls hoist, everything
else still flows source-order.

### 6. Interaction with the value restriction

Inside one SCC: each member is initially monomorphic, gets
generalised at the SCC boundary. `infer_function_group`'s pass 2
already does this. No change.

Between SCCs: a non-function statement between SCC₁ and SCC₂ flows
in source order, can call into SCC₁'s generalised types, and SCC₂

### 7. Interaction with the value restriction

Inside one SCC: each member is initially monomorphic, gets
generalised at the SCC boundary. `infer_function_group`'s pass 2
already does this. No change.

Between SCCs: a non-function statement between SCC₁ and SCC₂ flows
in source order, can call into SCC₁'s generalised types, and SCC₂
isn't typed yet — but SCC₂ has fresh TVars in the env, so calls
into SCC₂ unify against those. If a `const sep = f()` between two
function decls happens to constrain `f`'s polymorphic type, the
value restriction prevents `sep` from generalising further, but
`f` still gets its principal type at the SCC boundary. This is
correct and matches GHC's behaviour.

### 8. Modules and exports

`export function f` participates in hoisting today; nothing
changes. Cross-module imports already see `f`'s generalised scheme.
Within the module, the SCC analysis runs over the whole top-level
statement list, so `export function`s mix freely with internal
helpers. No new export-visibility decisions.

## Testing strategy

Three layers, mirroring the project's existing convention
(see `ARCHITECTURE.md` § "Testing"):

1. **Targeted unit tests** in `crates/inty/src/infer/tests.rs`:
   - Singleton-SCC chain (`a → b → c`, all non-recursive): asserts
     each gets its own principal scheme.
   - Two-member SCC (mutual recursion): asserts both schemes share
     a generalisation point and unify correctly.
   - Three-member SCC with mixed recursion patterns: catches
     subtle Tarjan bugs.
   - Forward reference through a `const`: the gap-4a test in
     `htmx_gaps.rs`, un-`#[ignore]`d.
   - Forward reference into an object literal property: gap-4b
     test, un-`#[ignore]`d.
   - IIFE library pattern: gap-4c test, un-`#[ignore]`d.

2. **Regression coverage**: every test in `infer/tests.rs` that
   currently relies on adjacent-only hoisting (search for
   `mixed_plain_and_export_functions_hoist_together` and
   neighbours) should still pass without modification. SCC
   inference subsumes adjacent grouping.

3. **Property check via the metamorphic harness**: extend the
   well-typed-program generator (`tests/metamorphic/`) with a
   "shuffle function decls" transform — generate a program, mutate
   it by moving non-function statements between function decls,
   assert the type of every binding is unchanged. Catches
   ordering-dependent inference bugs.

## Implementation plan

Three commits, each independently reviewable:

1. **AST utility: free-identifier walker.** Add
   `parser/free_idents.rs` with a single `free_identifiers(&Stmt)
   -> HashSet<String>` function and unit tests. No behaviour
   change. ~120 lines including tests.

2. **SCC analysis + integration.** Add
   `infer/features/functions::compute_scc_partition` and refactor
   `infer_stmt_list` to the three-pass shape above. Adjacent-group
   logic deleted; `infer_function_group` reused per SCC. Existing
   tests stay green; the three `htmx_gaps.rs` `hoisting_*` tests
   become regression tests (delete `#[ignore]`). ~250 lines net
   diff.

3. **Error buffering + source-order reporting.** Buffer type errors
   during SCC inference, sort by span before emit. Smaller, lower
   priority — can land after (2). ~100 lines.

Total: ~500 lines of net diff, mostly new code. The trickiest
piece is the free-identifier walker (lexical scope tracking through
nested functions and destructuring); the rest is mechanical.

## What we deliberately don't do

- **No general inter-binding SCC for `let`/`const`/`var`.** Only
  function decls hoist (ES § 9.2.10 + § 14.3); mixing
  `const a = b; const b = a;` stays an error to match the TDZ
  ReferenceError engines throw.
- **No Annex B sloppy-mode function-in-block semantics.** Strict
  mode only. Browsers in sloppy mode implement the legacy
  cross-update behaviour described in ES Annex B.3.2; new tools
  should not.
- **No type-class generalisation beyond what
  `infer_function_group` already does.** SCC just decides *which*
  bindings share a generalisation point; the per-group logic is
  unchanged.
- **No source-level rewrites.** This is purely an analysis change;
  the parser, AST, and surface syntax stay identical.

## Open questions

These are the remaining items that aren't pinned by ECMAScript and
need a project-level decision:

1. **Free-identifier walker location.** Bespoke new module under
   `crates/inty/src/parser/`, or extend an existing AST visitor?
   Quick grep shows no existing one; default to a new module unless
   review surfaces something to reuse.
2. **Error type sentinel.** Introduce a proper `Type::Error` now,
   or use a fresh unconstrained TVar plus a buffered error as the
   substitute? Lean: defer the proper sentinel. The TVar substitute
   is sound (worst case: a downstream error references an
   unconstrained var, which is at most an extra noisy diagnostic,
   not a correctness bug).
3. **Error-emit order.** Sort buffered errors by source span before
   reporting, or report in SCC-topological order? Lean: source-span
   sort. ES error semantics aren't relevant here — engines stop at
   the first runtime error, but a type checker reports all
   statically-detectable problems, so the question is purely
   user-experience.
4. **Performance.** Tarjan is O(V+E); free-identifier walking is
   O(AST size). Per-scope, both are dominated by inference itself.
   No expected hotpath impact.
