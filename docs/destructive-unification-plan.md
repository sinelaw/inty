# Destructive unification for inty — implementation plan

Status: **plan / RFC** — no code yet. Companion to `docs/scaling.md`,
which sketches the migration at a high level. This document is the
concrete plan for executing Step 1 (Union-Find + destructive
unification), including data structures, the call-site map, the
rollback strategy, and the test ordering. Steps 2 (hash-consing) and
3 (lazy zonking) are layered on top and are out of scope here except
where they constrain decisions made now.

The plan is grounded in the standard literature on Hindley-Milner
inference at scale; the systems we mirror most closely are OCaml's
typechecker and GHC's constraint solver, both of which have decades
of production use on the workload classes we care about.

## 1. Problem recap

`Type::apply_subst` (`crates/inty/src/types/subst.rs:424`) is invoked
on every `state.unify` call (`unify.rs:22-24`), and `Subst::compose`
(`state.rs:744,773`) walks every existing binding once per new
binding. On `bigskysoftware/htmx@master/src/htmx.js` this combination
both blows the 8 MB main-thread stack (confirmed via `gdb` —
backtrace shows `Type::apply_subst → RowType::apply_subst →
FieldEntry::apply_subst` repeating ~14 native frames per logical
level) and burns 99 % CPU indefinitely (an `examples/infer_only`
binary with a 256 MB stack runs >11 min without finishing). The
existing `ApplySubstGuard` depth limit (256) is the right *idea* but
mis-calibrated: each logical level materialises far more than the
"~200 B per frame" the constant assumes.

`docs/scaling.md` § "Root cause" already attributes this to the
substitution-as-data model: O(N·S) per unification with N bindings
and type size S, executed K times, gives O(K·N·S) — for htmx, K, N
and S are all in the thousands.

## 2. The literature-backed fix

The fix the literature agrees on, used unchanged by OCaml, GHC,
Swift, TypeScript, rustc, and Roc, is:

1. **Destructive unification with Union-Find on type variables.**
   Robinson 1965 (the original unification algorithm) defined as a
   substitution; Martelli & Montanari 1982 ("An Efficient
   Unification Algorithm", ACM TOPLAS 4(2)) recast it as
   constraint-set rewriting suitable for a union-find
   implementation. Tarjan 1975 ("Efficiency of a Good but Not Linear
   Set Union Algorithm", JACM 22(2)) gives the α(n) data structure.
   The combination — destructive unification using union-find with
   path compression and union-by-rank — is what every production
   typechecker we listed uses.
2. **Trail-based rollback.** Warren 1983 (the WAM, §3.5 "The trail")
   for Prolog; OCaml mirrors this in `Btype.snapshot`/`backtrack`
   (`ocaml/typing/btype.ml`). On each destructive binding, push the
   pre-binding state onto a per-frame trail; on failure, pop the
   trail back to the saved point. This is the canonical way to make
   destructive unification composable with backtracking solvers like
   `subsume` and the type-class resolver.
3. **Rémy's level-based generalization** (Didier Rémy 1992,
   "Extension of ML Type System with a Sorted Equational Theory on
   Types", INRIA TR-1766; OCaml's implementation,
   `ocaml/typing/ctype.ml`; expository writeup: Oleg Kiselyov,
   "Efficient and Insightful Generalization",
   <https://okmij.org/ftp/ML/generalization.html>). Each type
   variable carries the binder-nesting level at which it was
   introduced; generalization at the end of a `let` quantifies
   exactly the variables whose level is strictly greater than the
   current outer level. This replaces the O(env) "free vars of the
   environment" computation that today's `generalize` does and is
   the correctness fix that the doc currently calls "generalise
   every free flex" (`state.rs:961`).
4. **Lazy zonking at boundaries** (Peyton Jones et al. 2007,
   "Practical Type Inference for Arbitrary-Rank Types", JFP 17(1) —
   the GHC paper that introduced the term "zonk"). Walk types only
   when an observer needs a fully-resolved shape: generalization,
   pretty-printing, type-class resolution, AST decoration.

Steps (1) and (2) are mandatory; they are what removes the O(N·S)
cost and the SIGSEGV. Step (3) is a correctness improvement that
removes a separate class of bugs (env-escape, over-generalization)
and incidentally makes the work in step (1) easier to land
correctly. Step (4) is a constant-factor optimisation on top of
(1).

## 3. Data structures

### 3.1 The variable table

```rust
// crates/inty/src/infer/var_table.rs   (new module)

pub type TVarId = u32;

#[derive(Clone, Debug)]
pub enum Resolution {
    /// Free root. May still be unified later.
    Unbound { level: Level, rank: u8 },
    /// Equivalence-class non-root: chase this to find the root.
    Link(TVarId),
    /// Bound to a structured type. Stays as a sink — once bound,
    /// reads zonk through it.
    Bound(Type),
}

pub struct VarTable {
    cells: Vec<Resolution>,
    /// The trail. Each entry records (id, previous resolution).
    /// On rollback we restore `cells[id] = prev` in reverse order
    /// up to a saved length.
    trail: Vec<(TVarId, Resolution)>,
}
```

Operations:

- `fresh(level) -> TVarId` — push `Unbound { level, rank: 0 }`.
- `find(id) -> TVarId` — chase `Link`s with path compression
  (writes through the trail).
- `root(id) -> &Resolution` — `cells[find(id)]`.
- `bind(id, ty)` — `find(id)`; require `Unbound`; trail-log; write
  `Bound(ty)`.
- `union(a, b)` — `find` both; if equal, done; otherwise
  union-by-rank with trail-log on both cells.
- `snapshot() -> TrailMark` / `restore(mark)` — for rollback.

Path-compression writes go through the trail too. This is OCaml's
discipline; without it, a compression that happens inside a
to-be-rolled-back branch leaves a stale `Link` pointing at a
resurrected `Unbound`.

### 3.2 Levels

```rust
pub type Level = u32;

// On InferState:
//   current_level: Level
// Bumped on entry to a let-RHS (or function body) being inferred for
// generalization; restored on exit. `fresh` reads it.
```

`generalize(ty)` then walks `ty`, zonks each variable, and quantifies
those whose `level > outer_level`. No environment walk required.
This is the Rémy / Kiselyov scheme.

### 3.3 Zonk

```rust
// crates/inty/src/infer/zonk.rs   (new module)

pub fn zonk(table: &VarTable, ty: &Type) -> Type;
```

Recursive structural walk mirroring today's `Type::apply_subst`, but:

- For `Type::Var(Flex(id))`, calls `table.find(id)` then matches on
  the resolution: `Unbound → Type::Var(Flex(root))`, `Bound(t) → zonk(t)`.
- For `Type::Var(Skolem(_))`, identity (skolems can't be bound).
- The recursive walk still needs depth protection on adversarial
  input (e.g. `type T = { x: { x: { x: ... }}}` 100k deep). Keep the
  existing `ApplySubstGuard` but tune the cap — without Union-Find
  overhead each logical level uses ~14 native frames; in `zonk` it
  drops to ~6 because the substitution lookup is no longer a HashMap
  hash. Recalibrate after measurement.
- A `zonk_into(table, ty, out)` variant that writes into a
  pre-allocated `Vec`-buffered builder may help once we measure
  allocation pressure, but is not required for correctness.

## 4. Unification, restated

```rust
fn unify(&mut self, span: Span, a: &Type, b: &Type) -> UnifyResult<()> {
    // Chase variables to roots, but do not zonk recursively — the
    // structural cases recurse and will chase on their own subterms.
    let a = self.shallow_root(a);   // returns Var(root) or Bound's content
    let b = self.shallow_root(b);
    match (a, b) {
        // Same variable (after chase): nothing to do.
        (Type::Var(Flex(x)), Type::Var(Flex(y))) if x == y => Ok(()),

        // Two distinct unbound variables: union, biased by rank;
        // the surviving root keeps the smaller level (since the
        // shared equivalence class outlives the deeper binder).
        (Type::Var(Flex(x)), Type::Var(Flex(y))) => self.union(x, y),

        // Variable vs structured: occurs check against the *root*
        // of every Flex in `t`, then bind.
        (Type::Var(Flex(x)), t) | (t, Type::Var(Flex(x))) => {
            self.occurs_check(x, &t)?;
            // Adjust levels: every Flex in t with level > our level
            // gets lowered to our level (Rémy: prevents escape).
            self.adjust_levels(&t, self.cells[x].level());
            self.bind(x, t);
            Ok(())
        }

        // Structural cases — same shape as today's unify_impl,
        // minus the apply_subst call at the top.
        ...
    }
}
```

The `apply_subst` calls at the top of today's `unify`
(`unify.rs:22-24`) go away: `shallow_root` is constant-time, and
recursion handles deeper structure.

`occurs_check` walks `t`, chasing each `Flex` to its root, and
fails if the target root equals `x`. This is `O(size of t · α(n))`
but only runs once per binding — no longer per-unification
amortised quadratic work.

## 5. Rollback

Two callers backtrack today (or want to): `subsume` and the
type-class constraint solver.

```rust
let mark = state.var_table.snapshot();
match state.try_match(...) {
    Ok(()) => { /* keep */ }
    Err(_) => state.var_table.restore(mark),
}
```

`restore` pops trail entries until the length matches `mark`, writing
each saved `(id, prev)` back into `cells`. O(rolled-back-bindings).

The existing `Subst::compose` callers that emulate rollback today by
*not* composing on a failure path become trivial.

## 6. Call-site map

The migration touches the entire `infer` module. Mechanical (renames
+ delete) for ~90 % of sites; the interesting work is concentrated.

| File | LoC change shape | Notes |
|---|---|---|
| `types/subst.rs` | delete `Subst`, `compose`, `Substitutable` for `Type`; keep `PresenceSubst` | Presence vars stay as a small subst since they have no structural recursion |
| `infer/var_table.rs` | **new** | Union-Find + trail |
| `infer/zonk.rs` | **new** | Replaces `Type::apply_subst` |
| `infer/state.rs` | replace `main_subst: Subst` with `var_table: VarTable`; rewrite `generalize` for levels; rewrite `instantiate` to use `fresh(current_level)` | Hot path |
| `infer/unify.rs` | rewrite per § 4 above | The interesting work |
| `infer/features/*.rs` | s/apply_subst/zonk/ ; remove explicit subst plumbing | Mechanical (~30 sites) |
| `infer/narrow.rs` | s/apply_subst/zonk/ | Mechanical |
| `types/tidy.rs` | add depth guard or convert to explicit stack (same problem, smaller blast radius) | Optional follow-up |
| `types/pretty.rs` | add cycle detection (with hash-consing in step 2 this becomes free) | Optional follow-up |
| `meta/soundness.rs` | s/apply_subst/zonk/ | Mechanical |

`grep -rn "apply_subst" crates/inty/src --include="*.rs" | wc -l`
gives **304** call sites today; rough estimate from a sample is
~270 of those are pure renames.

## 7. Test ordering

The 380 lib + ~60 integration tests are the harness. Order the
landing so the harness catches regressions early:

1. **VarTable + zonk in isolation.** New module, new unit tests.
   No production call sites yet. Property-test against the existing
   `Subst::apply_subst` for randomly generated bindings: `zonk(table,
   ty) == apply_subst(equivalent_subst, ty)` for any non-cyclic
   binding set.
2. **Switch `unify` to destructive**, keep `Subst` as a shim that
   delegates to `VarTable`. Run the full lib test suite at this
   point; any regression here is a bug in (1) or in the new `unify`.
3. **Delete the shim, rename `apply_subst` → `zonk` everywhere.**
   Mechanical commit; should be diff-only.
4. **Add Rémy levels.** This is a separate correctness change and
   can be done before or after the rename, but doing it after
   guarantees that any test failure isolates to the levels work.
5. **Tune the depth guard on `zonk`** based on measurements; remove
   the now-unused `Subst::compose` codepath.
6. **Run htmx end-to-end** as a new integration test (probably as
   a smoke test gated on its presence, since htmx is third-party).

Each step is a separate commit (and PR if you want). Steps 1–2 are
the hard ones; 3–6 are nearly diff-only.

## 8. Interactions to get right

### 8.1 Row polymorphism (Rémy 1994)

The current row representation (`RowType { props, tail }` with
`RowTail::Open(TVarName)`) is unchanged. Row unification (`unify_rows`,
`unify.rs:306`) already treats the tail variable as a unification
variable; under destructive unification, `RowTail::Open(v)` becomes
"chase `v` through the table." The Rémy presence variables are a
separate substitution domain today (`Subst::presences`); keep them as
a small dense `PresenceTable` with the same Union-Find treatment, or
keep the existing eager substitution since they don't recurse
structurally.

### 8.2 Equi-recursive types (`Type::Named`, `RowTail::Recursive`)

These are nominal references into the `state.type_defs` arena. The
arena is unaffected by the variable model change. The occurs-check
must treat `Type::Named(id, args)` as opaque for the purpose of
detecting variable cycles — unrolling it during occurs would
diverge — which is the convention today. Add a regression test that
unifies a row containing `Named(0, [α])` with `Named(0, [Number])`
and confirms `α := Number` without unrolling.

### 8.3 Type classes

`resolve_constraints` (`state.rs`) walks accumulated predicates. With
destructive unification, "the type at predicate-creation time" and
"the type at resolution time" differ by all the bindings that
happened in between — exactly the point of the model. Zonk each
predicate before attempting resolution, and re-trail on speculative
instance matches.

### 8.4 Skolems and rigid variables

`TVarName::Skolem(_)` represents a rigid variable from a
user-written annotation. Skolems are never bound; the union-find
machinery only touches `Flex`. Two skolems with the same id unify;
distinct skolems do not. No change.

### 8.5 The `Type::Error` recovery sentinel

Today `Type::apply_subst` returns `Type::Error` when the depth cap
fires (`subst.rs:431`). `zonk` keeps the same convention. The
`unify` rule `(Type::Error, _) | (_, Type::Error) => Ok(())`
(`unify.rs:36`) is unchanged — error absorption is orthogonal.

## 9. Risks

- **`subsume` is the hardest function to migrate.** It does
  speculative matching with backtracking already; getting the trail
  discipline right requires care. Mitigation: lift the
  snapshot/restore pattern into a `try_unify` helper and route every
  speculative path through it.
- **Path-compression on the trail can leak memory** if the inference
  pass holds the trail forever. Reset the trail at well-defined
  boundaries (top of `infer_program`, after each top-level
  `Stmt::Var` in the SCC pass). OCaml does the same — they reset at
  each top-level definition.
- **The "generalize every free flex" simplification at
  `state.rs:961`** is correctness-equivalent to levels only if no
  flex variable can escape its binder. With levels, this becomes
  enforced by construction. The migration order matters: introduce
  levels *before* relying on them for generalization, or accept that
  one test class (probably the higher-rank tests) flips behaviour at
  the levels step.
- **htmx may still be slow** — the asymptotic fix removes O(K·N·S),
  but the *type itself* is large. Expect "seconds" not "instant" on
  htmx after this lands. If that's not good enough, that's when
  step 2 (hash-consing) earns its keep.

## 10. What this plan deliberately does **not** include

- Hash-consing (`docs/scaling.md` § Step 2). Separate PR, separate
  motivation (memory + constant factor).
- Lazy zonking at boundaries (`docs/scaling.md` § Step 3).
  Optimisation on top of this work.
- Changing the representation of `Type` itself (from `Box`-recursive
  enum to arena indices). Required by hash-consing, premature now.
- Changing the type-class solver from constraint-list to
  type-directed (à la Wadler-Blott). Orthogonal to the variable
  model.

## 11. Estimated effort

- Step 1 (this plan): 2–3 days of focused work in the type system,
  plus ~1 day of call-site fallout. Matches `docs/scaling.md`'s
  estimate.
- Step 2 (hash-consing): 3–5 days, mostly because every `Type::Row
  {...}` literal in the codebase has to route through a constructor.
- Step 3 (lazy zonking): 1–2 days once 1 and 2 are in place.

## 12. References

- Robinson, J. A. 1965. "A Machine-Oriented Logic Based on the
  Resolution Principle." JACM 12(1).
- Martelli, A., Montanari, U. 1982. "An Efficient Unification
  Algorithm." ACM TOPLAS 4(2).
- Tarjan, R. E. 1975. "Efficiency of a Good but Not Linear Set Union
  Algorithm." JACM 22(2).
- Warren, D. H. D. 1983. "An Abstract Prolog Instruction Set."
  Technical Note 309, SRI International. (§ 3.5 The Trail.)
- Damas, L., Milner, R. 1982. "Principal Type Schemes for Functional
  Programs." POPL '82.
- Rémy, D. 1992. "Extension of ML Type System with a Sorted
  Equational Theory on Types." INRIA Research Report RR-1766.
- Rémy, D. 1994. "Type Inference for Records in a Natural Extension
  of ML." In *Theoretical Aspects of Object-Oriented Programming*.
  (The row-polymorphism paper inty already cites.)
- Peyton Jones, S., Vytiniotis, D., Weirich, S., Shields, M. 2007.
  "Practical Type Inference for Arbitrary-Rank Types." JFP 17(1).
  (Source of the "zonk" terminology.)
- Filliâtre, J.-C., Conchon, S. 2006. "Type-Safe Modular
  Hash-Consing." ML Workshop '06.
- Kiselyov, O. "Efficient and Insightful Generalization."
  <https://okmij.org/ftp/ML/generalization.html>. (Expository
  writeup of the Rémy levels scheme.)
- OCaml typechecker: `ocaml/typing/ctype.ml` (unification),
  `ocaml/typing/btype.ml` (trail).
- GHC: <https://gitlab.haskell.org/ghc/ghc>,
  `compiler/GHC/Tc/Solver/Monad.hs` (constraint solver),
  `compiler/GHC/Tc/Utils/TcMType.hs` (zonking).
- rustc: <https://github.com/rust-lang/rust>,
  `compiler/rustc_infer/src/infer/` (inference variables in a
  union-find table).
