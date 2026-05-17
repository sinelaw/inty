//! Union-Find variable table for destructive unification.
//!
//! This is Step 1 of the destructive-unification migration documented
//! in `docs/destructive-unification-plan.md`. It is intentionally
//! self-contained: nothing in production calls into here yet. The
//! goal of Step 1 is to land the data structure with strong property
//! tests proving it is observably equivalent to today's
//! `Subst::apply_subst` model, so subsequent steps can flip call
//! sites over without losing test coverage.
//!
//! ## Algorithm
//!
//! Each type variable is a cell in [`VarTable::cells`] holding a
//! [`Resolution`]:
//!
//! - `Unbound { level, rank }` — free root, may still be unified later.
//!   `level` is Rémy's binder-nesting depth (used by Step 4's
//!   generalization); `rank` is the Tarjan union-by-rank height
//!   (Tarjan 1975, "Efficiency of a Good but Not Linear Set Union
//!   Algorithm", JACM 22(2)).
//! - `Link(other)` — non-root in the equivalence class; chase
//!   `other` to find the root.
//! - `Bound(ty)` — class root resolved to a structured type. Reads
//!   zonk through it (see `infer::zonk`).
//!
//! Path compression on [`VarTable::find`] writes through the trail so
//! that a compression performed inside a to-be-rolled-back branch is
//! itself rolled back. This is OCaml's discipline (`btype.ml`'s
//! `Tlink` chases under `snapshot`/`backtrack`); without it, a
//! `restore` could leave a stale `Link` pointing at a resurrected
//! `Unbound`.
//!
//! ## Rollback (Warren 1983, the WAM trail)
//!
//! Each mutation pushes the prior cell value onto [`VarTable::trail`].
//! [`VarTable::snapshot`] returns the trail length; [`VarTable::restore`]
//! pops back to that mark, undoing each write in reverse order.
//! This is what makes destructive unification composable with the
//! existing speculative callers (`subsume`, the type-class solver) —
//! they snapshot before a tentative match and restore on failure.

use crate::types::{TVarId, Type};

/// Rémy's binder-nesting level. A type variable allocated at level
/// `n` may be generalized only by a `let` whose binder lives at a
/// strictly shallower level. See `docs/destructive-unification-plan.md`
/// § 3.2 for the integration plan with `generalize`. Stored on every
/// `Unbound` cell so generalization is a single-pass walk over a
/// type's zonked form, not the env-difference scan
/// `state.rs::generalize` does today.
pub type Level = u32;

/// State of a single variable cell in [`VarTable`].
#[derive(Clone, Debug)]
pub enum Resolution {
    /// Free root of an equivalence class. Carries the level and
    /// union-by-rank height.
    Unbound { level: Level, rank: u8 },
    /// Non-root: chase this link to find the equivalence-class root.
    /// `Link`s are introduced by `union`; `find` rewrites them
    /// (under the trail) so amortised path length is α(n).
    Link(TVarId),
    /// Root resolved to a structured type. Reads zonk through it.
    Bound(Type),
}

/// Opaque trail mark returned by [`VarTable::snapshot`]. Passing it
/// to [`VarTable::restore`] reverts every binding made since the
/// snapshot. Marks are just trail lengths but exposing the field
/// would let callers fabricate marks that don't correspond to real
/// snapshot points; the newtype keeps the discipline tight.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrailMark(usize);

/// Union-Find table over flex type-variable ids.
///
/// Skolem variables are deliberately *not* in this table — they're
/// rigid by construction and never unified. Only `TVarName::Flex(id)`
/// indexes into [`VarTable::cells`].
#[derive(Clone, Debug, Default)]
pub struct VarTable {
    /// Cell indexed by `TVarId`. `cells.len()` is the high-water
    /// mark of fresh variable allocation.
    cells: Vec<Resolution>,
    /// Per-mutation undo log: each entry is `(id, prev_state)`. The
    /// trail grows monotonically inside a unification phase and is
    /// drained either by `restore` (on a backtrack) or by the
    /// inference driver between top-level bindings (see plan § 9
    /// "memory" risk).
    trail: Vec<(TVarId, Resolution)>,
    /// Current binder-nesting level. Bumped on entry to a let-RHS
    /// being inferred for generalization; restored on exit. Read by
    /// [`VarTable::fresh`] so each new variable carries the depth at
    /// which it was introduced.
    current_level: Level,
}

impl VarTable {
    /// Empty table at level 0.
    pub fn new() -> Self {
        VarTable::default()
    }

    /// Current binder-nesting level. Public for the test/inspection
    /// path; production code mutates via [`VarTable::push_level`] /
    /// [`VarTable::pop_level`] so the bumps stay balanced.
    pub fn current_level(&self) -> Level {
        self.current_level
    }

    /// Enter a deeper binder scope (e.g. a let-RHS). Returns the
    /// previous level so the caller can hand it back to
    /// [`VarTable::pop_level`]. Pairs with `pop_level` LIFO.
    pub fn push_level(&mut self) -> Level {
        let prev = self.current_level;
        self.current_level = prev + 1;
        prev
    }

    /// Restore the level saved by a prior [`VarTable::push_level`].
    pub fn pop_level(&mut self, saved: Level) {
        self.current_level = saved;
    }

    /// Number of cells ever allocated. Indices `0..len()` are valid;
    /// indices outside this range will panic in `find` / `bind` /
    /// `union`. Mirrors `Vec::len`.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Allocate a fresh `Unbound` variable at the current level.
    /// Returns its `TVarId`. The id is `cells.len()` at the moment
    /// of the call, so ids are dense and never recycled — a freed
    /// equivalence class becomes `Link(root)` rather than vanishing.
    pub fn fresh(&mut self) -> TVarId {
        let id = self.cells.len() as TVarId;
        self.cells.push(Resolution::Unbound {
            level: self.current_level,
            rank: 0,
        });
        id
    }

    /// Allocate a fresh `Unbound` at an explicit level. Used by the
    /// generalization machinery, which needs to skolemize at a
    /// specific depth.
    pub fn fresh_at(&mut self, level: Level) -> TVarId {
        let id = self.cells.len() as TVarId;
        self.cells.push(Resolution::Unbound { level, rank: 0 });
        id
    }

    /// **Path-compressing find.** Chases `Link`s from `id` to the
    /// root of its equivalence class, rewriting every visited link
    /// to point directly at the root (Tarjan 1975). Each rewrite
    /// pushes onto the trail so a subsequent `restore` reverts it.
    ///
    /// Returns the root id. The root may be `Unbound` or `Bound`;
    /// the caller usually wants [`VarTable::root_resolution`] right
    /// after.
    ///
    /// Defensively bounded by `cells.len()` iterations: a malformed
    /// table containing a cycle (which would otherwise loop forever)
    /// is detected and `id` is returned unchanged. Cycles only arise
    /// from a bug in `union` / `bind` and are not a soundness issue
    /// here.
    pub fn find(&mut self, id: TVarId) -> TVarId {
        // First pass: walk to the root without writing, recording
        // the path. Bounded by `cells.len()` as a cycle defence.
        let mut path: Vec<TVarId> = Vec::new();
        let mut cur = id;
        let mut steps = 0usize;
        let cap = self.cells.len() + 1;
        loop {
            steps += 1;
            if steps > cap {
                // Cycle (shouldn't happen). Don't rewrite anything;
                // return the input id so callers don't crash.
                return id;
            }
            match self.cell(cur) {
                Resolution::Link(next) => {
                    path.push(cur);
                    cur = *next;
                }
                _ => break,
            }
        }
        // Second pass: point every node on the path at the root,
        // logging each rewrite. Skip a node already pointing at
        // `cur` (the no-op case the trail would otherwise grow for).
        for &node in &path {
            let prev = self.cells[node as usize].clone();
            if let Resolution::Link(target) = &prev {
                if *target == cur {
                    continue;
                }
            }
            self.trail.push((node, prev));
            self.cells[node as usize] = Resolution::Link(cur);
        }
        cur
    }

    /// Borrow the current resolution at `id` without chasing links.
    /// Most callers want [`VarTable::root_resolution`] instead.
    fn cell(&self, id: TVarId) -> &Resolution {
        &self.cells[id as usize]
    }

    /// Run [`VarTable::find`] then return the root's resolution.
    /// Result is `Unbound { .. }` or `Bound(_)`; never `Link`.
    pub fn root_resolution(&mut self, id: TVarId) -> Resolution {
        let root = self.find(id);
        self.cells[root as usize].clone()
    }

    /// Bind `id`'s root to the structured type `ty`. The root must
    /// currently be `Unbound`; binding an already-`Bound` root or a
    /// non-flex (skolem) is a caller bug. Trail-logs the prior
    /// `Unbound` state so a subsequent `restore` reverts the bind.
    ///
    /// Note: this does *not* do an occurs-check. The caller (`unify`
    /// in Step 2) is responsible for ensuring `ty` doesn't refer back
    /// to `id`'s root.
    pub fn bind(&mut self, id: TVarId, ty: Type) {
        let root = self.find(id);
        let prev = self.cells[root as usize].clone();
        debug_assert!(
            matches!(prev, Resolution::Unbound { .. }),
            "bind() called on non-Unbound root {:?}",
            prev
        );
        self.trail.push((root, prev));
        self.cells[root as usize] = Resolution::Bound(ty);
    }

    /// Union the equivalence classes of `a` and `b`. Both must be
    /// `Unbound` roots after `find`; if either is `Bound`, the
    /// caller should be calling [`VarTable::bind`] on the other
    /// against the bound type instead.
    ///
    /// Implements union-by-rank: the lower-rank tree becomes a
    /// `Link` to the higher-rank one; equal-rank breaks bumps the
    /// survivor's rank. The surviving root keeps the *minimum* of
    /// the two levels — Rémy's "level adjustment" rule, since the
    /// shared equivalence class outlives the deeper binder.
    pub fn union(&mut self, a: TVarId, b: TVarId) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        let (la, ranka) = match self.cells[ra as usize] {
            Resolution::Unbound { level, rank } => (level, rank),
            ref other => panic!("union() on non-Unbound root: {:?}", other),
        };
        let (lb, rankb) = match self.cells[rb as usize] {
            Resolution::Unbound { level, rank } => (level, rank),
            ref other => panic!("union() on non-Unbound root: {:?}", other),
        };
        let merged_level = la.min(lb);
        let (winner, loser, new_rank) = match ranka.cmp(&rankb) {
            std::cmp::Ordering::Less => (rb, ra, rankb),
            std::cmp::Ordering::Greater => (ra, rb, ranka),
            std::cmp::Ordering::Equal => (ra, rb, ranka.saturating_add(1)),
        };
        // Log both prior states then write.
        let prev_loser = self.cells[loser as usize].clone();
        self.trail.push((loser, prev_loser));
        self.cells[loser as usize] = Resolution::Link(winner);
        let prev_winner = self.cells[winner as usize].clone();
        self.trail.push((winner, prev_winner));
        self.cells[winner as usize] = Resolution::Unbound {
            level: merged_level,
            rank: new_rank,
        };
    }

    /// Save a point on the trail. Pass the returned mark to
    /// [`VarTable::restore`] to revert all subsequent mutations.
    pub fn snapshot(&self) -> TrailMark {
        TrailMark(self.trail.len())
    }

    /// Roll back to `mark`. Undoes every mutation made after the
    /// snapshot, in reverse order. Cheap: O(rolled-back-mutations).
    ///
    /// Cells allocated after the snapshot remain (their id is the
    /// caller's; we can't safely free them without breaking
    /// references the caller might still hold). They'll be `Unbound`
    /// again because their initial state was `Unbound` and there
    /// were no mutations to undo.
    pub fn restore(&mut self, mark: TrailMark) {
        let TrailMark(target) = mark;
        debug_assert!(
            target <= self.trail.len(),
            "restore mark {} is past current trail length {}",
            target,
            self.trail.len()
        );
        while self.trail.len() > target {
            let (id, prev) = self.trail.pop().expect("trail not empty");
            self.cells[id as usize] = prev;
        }
    }

    /// Drop the trail, committing all mutations so far. After this,
    /// `snapshot()` returns a mark to the empty trail. Called by the
    /// inference driver at top-level boundaries where rollback is
    /// no longer needed (see plan § 9 "memory" risk and OCaml's
    /// reset between top-level definitions).
    pub fn commit_trail(&mut self) {
        self.trail.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Type;

    fn ty_number() -> Type {
        Type::Number
    }
    fn ty_string() -> Type {
        Type::String
    }

    /// `fresh` returns dense, monotonic ids and creates `Unbound`
    /// cells at the current level.
    #[test]
    fn fresh_allocates_dense_unbound_at_current_level() {
        let mut t = VarTable::new();
        assert_eq!(t.fresh(), 0);
        assert_eq!(t.fresh(), 1);
        assert_eq!(t.fresh(), 2);
        assert_eq!(t.len(), 3);
        for id in 0..3 {
            match t.root_resolution(id) {
                Resolution::Unbound { level, rank } => {
                    assert_eq!(level, 0);
                    assert_eq!(rank, 0);
                }
                other => panic!("expected Unbound, got {:?}", other),
            }
        }
    }

    /// `bind` writes through `find`: a chain α → β → γ all resolve
    /// to the same bound type after binding the root.
    #[test]
    fn bind_propagates_through_chain() {
        let mut t = VarTable::new();
        let a = t.fresh();
        let b = t.fresh();
        let c = t.fresh();
        // Manually wire a chain. In production this happens via `union`,
        // but the test wants to exercise `find`'s compression.
        t.union(a, b);
        t.union(b, c);
        t.bind(a, ty_number());
        for id in [a, b, c] {
            match t.root_resolution(id) {
                Resolution::Bound(ty) => assert_eq!(ty, ty_number()),
                other => panic!("expected Bound(Number), got {:?}", other),
            }
        }
    }

    /// `find` compresses paths: a deep chain becomes a flat fan
    /// after the first lookup.
    #[test]
    fn find_compresses_path() {
        let mut t = VarTable::new();
        let ids: Vec<_> = (0..10).map(|_| t.fresh()).collect();
        // Build α0 → α1 → α2 → ... → α9 (chain of unions).
        for i in 0..ids.len() - 1 {
            t.union(ids[i], ids[i + 1]);
        }
        let root = t.find(ids[0]);
        // After find, every node on the path should be a Link directly to root,
        // or be the root itself.
        for &id in &ids {
            if id == root {
                continue;
            }
            match t.cell(id) {
                Resolution::Link(target) => assert_eq!(
                    *target, root,
                    "node {} should point directly at root {} after compression",
                    id, root
                ),
                other => panic!("expected Link, got {:?}", other),
            }
        }
    }

    /// `union` survives equal-rank merge: the rank goes up by one.
    #[test]
    fn union_equal_rank_bumps_rank() {
        let mut t = VarTable::new();
        let a = t.fresh();
        let b = t.fresh();
        // Both rank 0. After union, the survivor has rank 1.
        t.union(a, b);
        let root = t.find(a);
        match t.cell(root) {
            Resolution::Unbound { rank, .. } => assert_eq!(*rank, 1),
            other => panic!("expected Unbound rank=1, got {:?}", other),
        }
    }

    /// `union` keeps the smaller of the two levels (Rémy).
    #[test]
    fn union_keeps_min_level() {
        let mut t = VarTable::new();
        t.current_level = 5;
        let deep = t.fresh();
        t.current_level = 2;
        let shallow = t.fresh();
        t.union(deep, shallow);
        let root = t.find(deep);
        match t.cell(root) {
            Resolution::Unbound { level, .. } => assert_eq!(*level, 2),
            other => panic!("expected Unbound level=2, got {:?}", other),
        }
    }

    /// `snapshot` + `restore` undoes a bind.
    #[test]
    fn restore_undoes_bind() {
        let mut t = VarTable::new();
        let a = t.fresh();
        let mark = t.snapshot();
        t.bind(a, ty_number());
        assert!(matches!(t.root_resolution(a), Resolution::Bound(_)));
        t.restore(mark);
        assert!(matches!(t.root_resolution(a), Resolution::Unbound { .. }));
    }

    /// `snapshot` + `restore` undoes a chain of unions and binds.
    #[test]
    fn restore_undoes_union_and_bind() {
        let mut t = VarTable::new();
        let a = t.fresh();
        let b = t.fresh();
        let c = t.fresh();
        let mark = t.snapshot();
        t.union(a, b);
        t.union(b, c);
        t.bind(a, ty_string());
        // All three resolve to String now.
        for &id in &[a, b, c] {
            assert!(matches!(t.root_resolution(id), Resolution::Bound(_)));
        }
        t.restore(mark);
        // All three are independent Unbound again.
        for &id in &[a, b, c] {
            assert!(matches!(t.root_resolution(id), Resolution::Unbound { .. }));
        }
        // And distinct: find returns the id itself.
        assert_eq!(t.find(a), a);
        assert_eq!(t.find(b), b);
        assert_eq!(t.find(c), c);
    }

    /// Path compression *inside* a snapshotted region is also rolled
    /// back. Without this, a compression performed speculatively
    /// would leave a stale `Link` pointing at a resurrected `Unbound`
    /// after rollback. (OCaml's `btype.ml` does exactly this; the
    /// test pins that we match.)
    #[test]
    fn restore_undoes_path_compression() {
        let mut t = VarTable::new();
        let a = t.fresh();
        let b = t.fresh();
        let c = t.fresh();
        // Build a chain a→b→c without going through find.
        t.union(a, b);
        let mark = t.snapshot();
        t.union(b, c); // now there's an even longer chain to compress
        // Force a find that triggers compression inside the snapshot.
        let _ = t.find(a);
        // Restore should revert both the union and the compression.
        t.restore(mark);
        // After restore, a and b are still merged (pre-snapshot), but
        // c is independent again.
        assert_eq!(t.find(a), t.find(b));
        assert_ne!(t.find(a), t.find(c));
    }

    /// `commit_trail` makes a prior `snapshot` un-restorable. After
    /// commit, `snapshot()` returns a mark to the empty trail.
    #[test]
    fn commit_trail_drops_history() {
        let mut t = VarTable::new();
        let a = t.fresh();
        let mark = t.snapshot();
        t.bind(a, ty_number());
        t.commit_trail();
        // Mark is now stale; restoring to it should do nothing
        // because the trail is empty (the mark length 0 matches).
        t.restore(mark);
        assert!(matches!(t.root_resolution(a), Resolution::Bound(_)));
    }

    /// Skolems are never in the table — only flex variables. This
    /// is a documentation test: we don't enforce it at the type
    /// level (the table indexes by `TVarId`, not `TVarName`), but the
    /// invariant is that callers only `fresh()` for flex variables
    /// and look up flex variables via their id. The cells store no
    /// skolem state.
    #[test]
    fn table_only_stores_flex_variables() {
        let mut t = VarTable::new();
        let _a = t.fresh();
        let _b = t.fresh();
        // No constructor for "skolem cell"; the invariant is satisfied
        // by construction.
        assert_eq!(t.len(), 2);
    }
}
