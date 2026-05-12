# SCC-based binding inference

Design sketch for replacing inty's adjacent-function-decl hoisting with
dependency-driven strongly-connected-component (SCC) inference,
following the standard approach from the ML/Haskell lineage. The
motivation is gap 4 in [`crates/inty/tests/htmx_gaps.rs`](../crates/inty/tests/htmx_gaps.rs)
(the IIFE library pattern used by htmx, jQuery, lodash, Day.js, etc.).
Status: design only — no code yet.

## Problem recap

Today `infer_stmt_list` (in `src/infer/mod.rs`) walks statements
left-to-right and groups *contiguous* `function` declarations into a
binding group. `infer_function_group` does textbook let-rec inference
on each group: hoist names → infer all bodies → generalise. Any
non-function statement between two `function` decls breaks the group,
so a forward reference across the break fails with "Undefined
variable". That's what blocks every htmx-shaped file.

The standard fix is dependency analysis: hoist *every* `function`
declaration in a scope before inferring any body, then process
mutually-recursive sub-groups (SCCs of the call graph) in topological
order.

## Target rule

In a scope with bindings B₁ … Bₙ in source order:

1. Pre-pass — collect every **hoistable** binding into a name map
   with a fresh monomorphic type variable. Hoistable = `function f`
   declarations and `export function f` declarations (matches JS's
   `function`-decl hoisting; `var`/`let`/`const` initialisers are
   not hoistable because of TDZ / late-init).
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
type-checks regardless of source ordering.

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

## Subtle points worth pinning before coding

### 1. Scope boundaries

Hoisting is **per function scope** in JS. inty's existing
`infer_stmt_list` is called recursively from `Stmt::Block` and from
`infer_function` (for function bodies). The pre-pass must collect
only function decls *directly* in the current statement list — not
those nested inside `if`/`for`/etc. blocks. Nested `function` decls
inside blocks hoist to their *containing block* per ES2015 strict
mode, but inty's current behaviour matches the "hoist to function"
convention; we should keep that unchanged.

**Decision needed**: confirm we want to hoist function decls inside
`if`/`for` blocks to the immediate containing scope or to the
containing function. Today's code hoists to the block (block is its
own `infer_stmt_list` call). The pre-pass per call site preserves
that, which is fine.

### 2. `var f = function() {…}` is *not* hoistable

Even though `var f` is name-hoisted to `undefined`, the function
value is only assigned when the line executes. A call to `f()`
before the `var f = …` line is a runtime TypeError. Treating this
as hoistable would type-check programs that crash. Decision: keep
the current treatment — only `function` and `export function`
declarations are hoistable.

### 3. Class declarations

Once class declarations land in inty's scope (currently `class C {…}`
is a value, not a hoisted decl), the same question applies. ES
class declarations are TDZ — *not* hoisted. Keep them out of the
hoistable set.

### 4. Error spans and ordering

A type error inside a late-in-source, early-in-topo SCC will get
inferred before the user's mental source-order walk reaches it.
Two options:

  (a) Collect all SCC errors, sort by source span, report in source
      order. Matches user expectations; needs an error buffer.
  (b) Report in topo order, accept that error spans may go
      "backwards." Simpler; OCaml does this.

**Recommendation**: (a). inty already buffers parse errors
internally; same shape works for type errors. Cost is one
small refactor of the error path.

### 5. Cross-SCC type errors

If `f` (in SCC₁) calls `g` (in SCC₂), and SCC₂ has a type error,
we want SCC₁ to still be inferred (best-effort). Standard practice:
on an SCC failure, bind every member to `Type::Error` (a fresh
sentinel) and continue. This avoids cascading errors. inty doesn't
currently have a `Type::Error` sentinel; the simplest substitute is
a fresh unconstrained TVar plus an error in the buffer, which
preserves principal types for unrelated bindings.

**Decision needed**: introduce a proper error type, or live with
the TVar substitute.

### 6. TDZ ("use before init") diagnostics

Once `function` decls hoist freely, the existing "Undefined
variable" error stops firing for forward references — which is
the goal. But the same error currently doubles as a TDZ catch for
`let`/`const`. We don't lose that: `let`/`const` are not in the
hoistable set, so a use-before-decl of a `let` still hits the
existing path. No action needed.

The actual TDZ JS semantics for `function` decls inside blocks
(strict mode) is more nuanced, but inty doesn't currently model
strict-mode TDZ; out of scope.

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
  function decls hoist. Mixing `const a = b; const b = a;` stays
  an error (TDZ).
- **No effort to match TC39's block-level function declaration
  semantics.** inty's existing convention (hoist to nearest
  statement-list) is preserved.
- **No type-class generalisation beyond what
  `infer_function_group` already does.** SCC just decides *which*
  bindings share a generalisation point; the per-group logic is
  unchanged.
- **No source-level rewrites.** This is purely an analysis change;
  the parser, AST, and surface syntax stay identical.

## Open questions

1. Free-identifier walker — bespoke new module, or do we already
   have one I missed? (Quick grep says no, but worth a second look.)
2. Error type sentinel — introduce now or defer? (Lean: defer; the
   TVar substitute is fine for SCC failure cascades.)
3. Should `var f = function() {…}` participate as a "weak" hoist —
   visible only from later statements? Probably not worth the
   complexity; the workaround (use `function f() {}`) is trivial.
4. Performance: Tarjan is O(V+E); free-identifier walking is O(AST
   size). Per-scope, both are dominated by inference itself.
   No expected hotpath impact.
