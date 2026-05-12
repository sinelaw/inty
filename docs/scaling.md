# Scaling: deep types, large substitutions

Status: **design doc / RFC** — none of this is implemented yet. The
companion defensive fixes (depth limit in `Type::apply_subst`, worker
thread with larger stack) are implemented and live in
`crates/inty/src/types/subst.rs` and `crates/inty-cli/src/main.rs`;
they prevent SIGSEGV on adversarial input but do not address the
underlying scaling cost. This document is the path to fixing the
scaling cost itself.

## Symptom

Run inty against `bigskysoftware/htmx@master/src/htmx.js` (5,342 lines
of plain JS). With the multi-error + `delete` recovery in place
(commits `29f684a` and `920f933`), inference reaches the closing
`ready(function() { ... })` lambda at line 5,117. Inside that lambda,
the assignment `htmx.config = mergeObjects(htmx.config, metaConfig)`
forces an `apply_subst` over the `htmx` const's type, which by that
point in the file is a row with ~30 function-valued fields whose
bodies reference each other. The substitution map has accumulated
hundreds of bindings during inference. The combination produces a
type structure whose `apply_subst` walk:

- Overflows the default 8 MB stack (SIGSEGV) with a recursive call
  pattern `Type::apply_subst → RowType::apply_subst → FieldEntry::apply_subst
  → Type::apply_subst → …` that consumes ~13 stack frames per level of
  nesting through `BTreeMap::from_iter`'s iterator machinery.
- Does not complete in 90 seconds even with a 512 MB stack — so the
  wall-clock cost is independent of stack size.

Bisect confirms this is a *scaling* issue, not a *correctness* one:
inference up to line 5,116 finishes in well under a second.

## What changes in this PR

Two defensive guards, neither of which fixes the scaling cost:

1. **Recursion-depth limit in `Type::apply_subst`** (constant 256).
   Past the limit, the function returns `Type::Error` and sets a
   thread-local overflow flag. The top of `infer_program_with_env`
   checks the flag and pushes a `TypeError::Module` diagnostic so the
   user sees `type too deep for the current type-checker, see
   docs/scaling.md` instead of a SIGSEGV.

2. **64 MB worker thread for the CLI's inference work.** The default
   Linux main-thread stack is 8 MB; rustc itself uses the same pattern
   (`RUST_MIN_STACK`). 64 MB is generous for the depth limit above
   and lets *legitimate* deep-but-not-pathological code through.

Together these make inty no-SIGSEGV on arbitrary input. They do not
make htmx finish in reasonable time — the wall-clock issue below is
what does that.

## Root cause: the substitution model

Inty currently represents the substitution as a `HashMap<TVarName,
Type>` and unifies via:

- `Subst::unify(a, b) -> Subst` — produces a *new* substitution
  describing how to make `a` and `b` equal.
- `Subst::compose(other) -> Subst` — composes the new substitution
  with the accumulated one, **applying the new substitution to every
  type in `other`** (`subst.rs:120`). This is O(N·S) where N is the
  number of bindings and S is the size of the largest bound type.

Every unification call composes. So after K unifications with average
type size S and ending substitution size N, total work is at minimum
O(K · N · S). For htmx, K and S both grow into the thousands.

The row-level `apply_subst` already tries to be "shallow on purpose"
(`subst.rs:430`) to dampen this, but with deep enough types — and
htmx's late code does build deep types via the SCC recovery binding
big rows together — the recursion dominates anyway.

This is the textbook formulation of Damas-Milner. It is easy to
reason about and easy to test. It is *not* the formulation any
production type-checker uses, because of exactly the scaling
problems above.

## What production type-checkers actually do

| System | Variable model | Substitution model | Type representation |
|---|---|---|---|
| OCaml | Union-Find via mutable type refs | None — destructive unification | Shared via refs |
| GHC | Mutable `IORef` per type-var (`TcRef`) | Lazy zonking | Mostly shared |
| Swift | Union-Find in the constraint solver | None | Interned via `TypeBase` |
| TypeScript | Mutable type graph; no separate substitution | None | Interned via `Type` IDs |
| Rust (rustc) | Inference variables in a Union-Find table | None — variables resolved on read | Interned via `Ty<'tcx>` in the `TyCtxt` arena |
| Roc | Union-Find | None | Interned subroots in the `Subs` table |

Every column says "no substitution map at all." All of them use some
combination of:

### 1. Destructive unification with Union-Find

Type variables are not values — they are *cells*. `unify(a, b)`
chases each operand to its root, then either points one root at the
other (variable case) or recurses structurally. There is no `Subst`
and no `compose`. Reading the current resolution of a variable is
O(α(N)) (essentially constant with path compression). The benefit
over inty's current model:

- `Subst::compose`'s O(N · S) per-step cost disappears entirely.
- `apply_subst` becomes `zonk`: a one-shot walk that resolves
  variables to their roots. It runs at points the surface API needs a
  fully-resolved type (generalisation, pretty-printing, type-class
  resolution), not on every unification.
- Rolling back a failed unification is harder (mutable state), but
  the trail-based approach Prolog and OCaml use handles this cleanly.

### 2. Hash-consing / interning

Every distinct type value is built through a constructor that
deduplicates: `mk_row(props)` first checks an arena for a matching
`RowType` and returns the existing reference. Structural equality
becomes pointer equality. Substitution walks become
walk-once-per-distinct-subtree. rustc's `Ty<'tcx>` and TypeScript's
internal type table both do this.

### 3. Lazy zonking

Instead of eagerly resolving variables on every unification, store
the resolution and walk types only when an observer needs a stable
shape. GHC formalises this; it cuts the constant factor on
substitution further.

## Migration plan for inty

These are independent steps. (1) on its own removes the dominant
asymptotic cost. (2) and (3) are layered improvements.

### Step 1 — Destructive unification

Surface-level work:

- `TVarName::Flex(id)` becomes a Union-Find handle. The store is on
  `InferState`: `var_table: UnionFind<TVarId, Resolution>` where
  `Resolution = Unresolved | Resolved(Type)`.
- `unify(a, b)`:
  - Chase each to its root.
  - If both are unresolved roots: `union(a, b)`.
  - If one is unresolved: bind it to the other (with occurs check).
  - If both resolved: recurse structurally.
- Replace every `state.apply_subst(&ty)` call with `state.zonk(&ty)`,
  which does the same recursive walk but reads variable resolutions
  from the Union-Find table.
- Delete `Subst::compose`. Delete the `Substitutable` trait's
  `apply_subst` (or shim it through `zonk`).
- Generalisation reads roots, not substitutions; the free-var
  computation walks the type once and skips variables resolved to
  things outside the env's free set.

Rollback: introduce a per-frame trail in `InferState`. Each binding
push records the variable's previous resolution; failure pops the
trail. This is what OCaml and SWI-Prolog do.

Estimated effort: 2–3 days for the core type system, plus a day
shaking out call-site fallout (most call sites just rename
`apply_subst` → `zonk`).

Risk: the existing test suite (380 lib + 60-ish integration tests)
acts as a strong harness. The translation is mechanical for ~90% of
the surface; the remaining 10% is `subsume` and the row-tail
unification, which are the interesting bits.

### Step 2 — Hash-consing

Once (1) is in place, an arena-of-types lets `Type` shrink from a
recursive enum to an `Idx` into an arena, with deduplication on
construction. Specialised constructors (`Type::row(props, tail)`,
`Type::array(elem)`, …) become `TyCtxt::mk_row(props, tail)`. Every
existing pattern match on `Type` becomes a match on the dereferenced
arena entry, which is a single indirection.

Benefits:

- `apply_subst` (now `zonk`) walks each distinct subterm at most once
  because the same `Idx` is shared everywhere.
- `unify`'s occurs check becomes constant-time on already-equal
  subterms (pointer equality).
- Memory: a typical htmx-shaped program drops from N copies of the
  `htmx` row to one shared `Idx`.

Cost: every constructor needs to go through `TyCtxt`. Touching every
`Type::Row {...}` literal in the codebase is significant churn.

### Step 3 — Lazy zonking

The `zonk` function from step 1 is run eagerly today (on every
`apply_subst` call-site). Replace eager `zonk` with on-demand zonking
at well-defined boundaries:

- Before generalisation (to read the type's final shape).
- Before pretty-printing.
- Before exporting decl types to the LSP / decoration pass.
- Before resolving a type-class constraint.

In between, types stay un-zonked. This is exactly what GHC calls
"zonking at the boundary."

Cost: small once (1) and (2) are done. Mostly the discipline of
auditing where zonking is required.

## Other related cleanups that fall out

- `free_vars` (`subst.rs:459` etc.) is also recursive over the same
  shape that `apply_subst` is. Once types are interned (step 2), it
  becomes walk-each-Idx-once with memoisation. Without interning,
  it's a candidate for the same depth limit as `apply_subst`.
- The `subsume` and `unify` functions also recurse structurally;
  they don't currently overflow on htmx but could on adversarially
  deep types. Once the Union-Find model is in, these become
  constant-frame-per-level instead of constant-frame-per-walk-step.
- The pretty-printer (`types/pretty.rs`) walks the same shape and
  can produce gigantic strings for deep types. With interning, it
  can detect already-rendered subtypes and emit references.

## When this should happen

It does not need to happen immediately. The defensive fixes in this
PR (depth limit + worker thread) cap inty's pathological behaviour
on arbitrary input at "report a clean diagnostic, exit non-zero,"
which is the same defensive contract TypeScript and rustc give. The
*performance* story stays poor on htmx-sized files until step 1.

Reasonable trigger: the first time inty needs to type-check a file
where the depth-limit diagnostic fires on legitimate code. Today
that's only htmx and friends. If users start running inty on more
big single-file libraries, that day will come.
