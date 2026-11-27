//! Substitution for type inference.
//!
//! Implements the substitution data structure and the Substitutable trait
//! for applying substitutions to types, type schemes, and other structures.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::ty::{
    FieldEntry, PVarName, Presence, PropName, QualType, RowTail, RowType, TVarName, Type, TypePred,
    TypeScheme,
};

/// Default cap on the recursion depth of `Type::apply_subst`. Past
/// this, the walk bails to `Type::Error` and sets the thread-local
/// [`APPLY_SUBST_OVERFLOWED`] flag so the inference driver can surface
/// a clean diagnostic. See `docs/scaling.md` for the rationale: the
/// real fix is destructive unification + interning; this limit only
/// converts a SIGSEGV on adversarial input into a controlled error.
///
/// 256 leaves headroom on the default Linux 8 MB stack
/// (~13 frames per nesting level × ~200 B per frame ≈ 660 KB at the
/// limit) and is well above the depth any reasonable JS produces.
/// The effective cap can be lowered by tests via
/// [`set_apply_subst_depth_limit_for_test`].
const DEFAULT_APPLY_SUBST_DEPTH: usize = 256;

thread_local! {
    /// Current recursion depth of `Type::apply_subst`. Bumped via the
    /// `ApplySubstGuard` RAII; reset to 0 when no walk is active.
    static APPLY_SUBST_DEPTH: Cell<usize> = const { Cell::new(0) };
    /// Effective depth cap. Defaults to [`DEFAULT_APPLY_SUBST_DEPTH`].
    /// Lowered by tests via [`set_apply_subst_depth_limit_for_test`]
    /// so the integration tests can drive the limit with shallow
    /// types (the parser itself recurses on deeply nested literals,
    /// so we can't fabricate a real 256-deep type via source).
    static APPLY_SUBST_LIMIT: Cell<usize> = const { Cell::new(DEFAULT_APPLY_SUBST_DEPTH) };
    /// Set to `true` whenever the depth limit was hit during the most
    /// recent inference run. The driver (`infer_program_with_env`)
    /// reads and clears this after the call to surface a clean
    /// diagnostic in place of the SIGSEGV the runaway recursion would
    /// otherwise cause.
    static APPLY_SUBST_OVERFLOWED: Cell<bool> = const { Cell::new(false) };
}

/// Returns true and clears the flag if a depth-limit overflow
/// happened in `Type::apply_subst` since the flag was last read.
pub fn take_apply_subst_overflow() -> bool {
    APPLY_SUBST_OVERFLOWED.with(|f| f.replace(false))
}

/// Lower the per-thread depth cap. Returns the previous value so the
/// caller can restore it. Tests only; production code should leave
/// the default in place.
#[doc(hidden)]
pub fn set_apply_subst_depth_limit_for_test(limit: usize) -> usize {
    APPLY_SUBST_LIMIT.with(|l| l.replace(limit))
}

/// RAII guard: increments [`APPLY_SUBST_DEPTH`] on construction
/// (returning `None` if the limit was reached), decrements on drop.
///
/// Exposed at `pub(crate)` so the new destructive-unification path
/// (`crate::infer::zonk`) shares the same depth bookkeeping —
/// otherwise a zonk-deep walk would not interact with the existing
/// "type too deep" diagnostic surfaced by
/// `infer_program_with_env`.
pub(crate) struct ApplySubstGuard;

impl ApplySubstGuard {
    pub(crate) fn try_enter() -> Option<Self> {
        APPLY_SUBST_DEPTH.with(|d| {
            let cur = d.get();
            let limit = APPLY_SUBST_LIMIT.with(|l| l.get());
            if cur >= limit {
                APPLY_SUBST_OVERFLOWED.with(|f| f.set(true));
                None
            } else {
                d.set(cur + 1);
                Some(ApplySubstGuard)
            }
        })
    }
}

impl Drop for ApplySubstGuard {
    fn drop(&mut self) {
        APPLY_SUBST_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

/// A substitution mapping type variables to types and presence
/// variables to presences (Remy '94 — two domains for one substitution).
#[derive(Clone, Debug, Default)]
pub struct Subst {
    /// Bound types are shared: the inference state's union-find table
    /// holds the same `Arc`, and path compression copies pointers.
    map: HashMap<TVarName, Arc<Type>>,
    presences: HashMap<PVarName, Presence>,
    /// Undo log (Warren's trail, as in `VarTable`): each mutation's
    /// prior entry, so a speculative branch is rolled back by undoing
    /// its writes instead of the caller cloning the whole map. `None`
    /// (the default) records nothing; the inference state's main
    /// substitution enables it (`with_trail`).
    trail: Option<Vec<SubstUndo>>,
    /// Each trail entry's serial number (never reused), so a
    /// [`SubstStamp`] can tell whether the writes before it are still in
    /// effect.
    serials: Vec<u64>,
    next_serial: u64,
    /// With a trail: for each variable, the variables a binding of which
    /// mentioned it (kept when the binding is undone or replaced, so a
    /// superset): see [`Self::may_reach`].
    mentioned_by: HashMap<TVarName, Vec<TVarName>>,
    /// Counts the writes and undos that can change what a type reaches
    /// (not path compression): see [`Self::version`].
    version: u64,
    /// Apply each binding once, not again to what it is bound to: a
    /// simultaneous substitution of parameters by arguments, which may
    /// mention the parameters themselves (`Subst::simultaneous`).
    simultaneous: bool,
}

/// One entry of [`Subst`]'s undo log: a key and what it mapped to
/// before a write (`None`: unbound).
#[derive(Clone, Debug)]
enum SubstUndo {
    Type(TVarName, Option<Arc<Type>>),
    /// Path compression (`resolve`): a binding replaced by the end of
    /// its chain, which reaches the same.
    Compressed(TVarName, Arc<Type>),
    Presence(PVarName, Option<Presence>),
}

/// A write to a [`Subst`], as [`Subst::writes_since`] lists it.
#[derive(Clone, Copy, Debug)]
pub enum SubstWrite<'a> {
    /// A variable that was free bound.
    Bound(&'a TVarName),
    /// A bound variable's binding replaced, or removed.
    Rebound(&'a TVarName),
    /// A binding replaced by the end of its chain (path compression), or
    /// by a link to a variable whose type is equal (`link_equal`): the free
    /// variables it reaches are the same.
    Compressed,
    /// A presence variable that was free bound.
    PresenceBound(&'a PVarName),
    /// A bound presence variable's binding replaced.
    PresenceRebound(&'a PVarName),
}

/// A point in a [`Subst`]'s trail, and the serial number of the write
/// just before it (see [`Subst::stamp`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubstStamp {
    len: usize,
    last: Option<u64>,
}

/// A point in a [`Subst`]'s undo log (see [`Subst::mark`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubstMark(usize);

impl Subst {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Subst {
            map: HashMap::new(),
            presences: HashMap::new(),
            trail: None,
            serials: Vec::new(),
            next_serial: 0,
            mentioned_by: HashMap::new(),
            version: 0,
            simultaneous: false,
        }
    }

    /// An empty substitution that records its writes, so it can be
    /// rolled back to a [`Subst::mark`] with [`Subst::undo_to`].
    /// An empty substitution applied simultaneously: a variable is
    /// replaced by its binding, which is not substituted again. For
    /// instantiating a named type's parameters with arguments that may
    /// mention those parameters (`Range<T>`'s body, unrolled at `T`).
    pub fn simultaneous() -> Self {
        Subst {
            simultaneous: true,
            ..Subst::empty()
        }
    }

    pub fn with_trail() -> Self {
        Subst {
            trail: Some(Vec::new()),
            ..Subst::empty()
        }
    }

    /// The current point of the undo log.
    pub fn mark(&self) -> SubstMark {
        SubstMark(self.trail.as_ref().map_or(0, Vec::len))
    }

    /// Undo every write made since `mark`, newest first. Cheap:
    /// O(writes undone).
    pub fn undo_to(&mut self, mark: SubstMark) {
        let Some(trail) = self.trail.as_mut() else {
            debug_assert!(false, "undo_to on a substitution without a trail");
            return;
        };
        while trail.len() > mark.0 {
            self.version += 1;
            self.serials.pop();
            match trail.pop().expect("trail not empty") {
                SubstUndo::Type(var, Some(prev)) | SubstUndo::Compressed(var, prev) => {
                    self.map.insert(var, prev);
                }
                SubstUndo::Type(var, None) => {
                    self.map.remove(&var);
                }
                SubstUndo::Presence(pvar, Some(prev)) => {
                    self.presences.insert(pvar, prev);
                }
                SubstUndo::Presence(pvar, None) => {
                    self.presences.remove(&pvar);
                }
            }
        }
    }

    /// Whether `ty` may reach `var` through the substitution: `false`
    /// only if it doesn't (it mentions neither `var` nor a variable whose
    /// binding, through others, does). Found from the variables whose
    /// bindings mention `var`, without walking what `ty` reaches (an
    /// object's whole type, for each variable bound to a type holding
    /// it); `true` when there are too many of those to look for. Without
    /// a trail (no index), always `true`.
    pub fn may_reach(&self, var: &TVarName, ty: &Type) -> bool {
        const MAX_MENTIONERS: usize = 512;
        if self.trail.is_none() {
            return true;
        }
        let mut found: HashSet<&TVarName> = HashSet::new();
        found.insert(var);
        let mut queue = vec![var];
        while let Some(v) = queue.pop() {
            for by in self.mentioned_by.get(v).into_iter().flatten() {
                if found.insert(by) {
                    if found.len() > MAX_MENTIONERS {
                        return true;
                    }
                    queue.push(by);
                }
            }
        }
        ty.any_var(&mut |v| found.contains(v))
    }

    /// Changes whenever what a type reaches through the substitution may
    /// have (a binding written, replaced or undone; not path compression,
    /// which keeps it): equal versions, equal reaches.
    pub fn version(&self) -> u64 {
        self.version
    }

    /// The current point of the trail, to list the writes since with
    /// [`Self::writes_since`].
    pub fn stamp(&self) -> SubstStamp {
        SubstStamp {
            len: self.serials.len(),
            last: self.serials.last().copied(),
        }
    }

    /// The writes made since `stamp`, oldest first, if the writes before
    /// it are all still in effect (`None` if one was undone since, or
    /// without a trail).
    pub fn writes_since(&self, stamp: SubstStamp) -> Option<Vec<SubstWrite<'_>>> {
        let trail = self.trail.as_ref()?;
        if self.serials.len() < stamp.len
            || stamp.len.checked_sub(1).map(|i| self.serials[i]) != stamp.last
        {
            return None;
        }
        Some(
            trail[stamp.len..]
                .iter()
                .map(|w| match w {
                    SubstUndo::Type(v, None) => SubstWrite::Bound(v),
                    SubstUndo::Type(v, Some(_)) => SubstWrite::Rebound(v),
                    SubstUndo::Compressed(..) => SubstWrite::Compressed,
                    SubstUndo::Presence(p, None) => SubstWrite::PresenceBound(p),
                    SubstUndo::Presence(p, Some(_)) => SubstWrite::PresenceRebound(p),
                })
                .collect(),
        )
    }

    /// Write `var ↦ ty`, logging the previous entry.
    fn write(&mut self, var: TVarName, ty: Arc<Type>) {
        self.version += 1;
        if self.trail.is_some() {
            let by = &mut self.mentioned_by;
            ty.any_var(&mut |u| {
                let list = by.entry(u.clone()).or_default();
                if list.last() != Some(&var) {
                    list.push(var.clone());
                }
                false
            });
        }
        let prev = self.map.insert(var.clone(), ty);
        if let Some(trail) = self.trail.as_mut() {
            trail.push(SubstUndo::Type(var, prev));
            self.serials.push(self.next_serial);
            self.next_serial += 1;
        }
    }

    /// Create a singleton substitution.
    pub fn singleton(var: TVarName, ty: Type) -> Self {
        let mut map = HashMap::new();
        map.insert(var, Arc::new(ty));
        Subst {
            map,
            presences: HashMap::new(),
            trail: None,
            serials: Vec::new(),
            next_serial: 0,
            mentioned_by: HashMap::new(),
            version: 0,
            simultaneous: false,
        }
    }

    /// Check if the substitution is empty in both domains.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty() && self.presences.is_empty()
    }

    /// [`Self::get`], sharing the binding.
    pub fn get_shared(&self, var: &TVarName) -> Option<Arc<Type>> {
        self.map.get(var).cloned()
    }

    /// Get the type for a variable, if present.
    pub fn get(&self, var: &TVarName) -> Option<&Type> {
        self.map.get(var).map(|t| &**t)
    }

    /// Path-compressing lookup. Chases `Type::Var → Type::Var → …`
    /// chains, rewriting every entry on the visited path to point
    /// directly at the chain's endpoint. Subsequent lookups of any
    /// variable on the chased path resolve in one hop.
    ///
    /// This is Tarjan path compression (Tarjan 1975, "Efficiency of
    /// a Good but Not Linear Set Union Algorithm"). The chain ends
    /// at either a structural type or an unbound variable; that
    /// endpoint becomes the new value of every entry on the path.
    /// Defensively bounded by a `visited` set so a malformed
    /// substitution (post-occurs-check this shouldn't happen) can't
    /// loop here.
    pub fn resolve(&mut self, var: &TVarName) -> Option<Arc<Type>> {
        let first = self.map.get(var)?.clone();
        if !matches!(*first, Type::Var(_)) {
            return Some(first);
        }

        let mut chain: Vec<TVarName> = vec![var.clone()];
        let mut current = first;
        let mut visited: HashSet<TVarName> = HashSet::new();
        visited.insert(var.clone());

        while let Type::Var(v) = &*current {
            let next_name = v.clone();
            if !visited.insert(next_name.clone()) {
                // Cycle (shouldn't happen post-occurs-check).
                // Leave the chain as-is; don't rewrite.
                return Some(current);
            }
            match self.map.get(&next_name).cloned() {
                Some(next) => {
                    chain.push(next_name);
                    current = next;
                }
                None => break, // unbound root
            }
        }

        // Path compression: point every entry on the chain at
        // `current`. Skip the final entry if it's the endpoint
        // itself (we don't want to write a binding for an unbound
        // variable).
        for k in &chain {
            let prev = self.map.insert(k.clone(), current.clone());
            if let Some(trail) = self.trail.as_mut() {
                trail.push(match prev {
                    Some(prev) => SubstUndo::Compressed(k.clone(), prev),
                    None => SubstUndo::Type(k.clone(), None),
                });
                self.serials.push(self.next_serial);
                self.next_serial += 1;
            }
        }
        Some(current)
    }

    /// Get the presence binding for a presence variable, if present.
    pub fn get_presence(&self, pvar: &PVarName) -> Option<&Presence> {
        self.presences.get(pvar)
    }

    /// Check if a type variable is in the domain.
    pub fn contains(&self, var: &TVarName) -> bool {
        self.map.contains_key(var)
    }

    /// Check if a presence variable is in the domain.
    pub fn contains_presence(&self, pvar: &PVarName) -> bool {
        self.presences.contains_key(pvar)
    }

    /// Replace a bound variable's binding by a link to another variable
    /// whose type unifying has just shown equal to it (`link_bound`):
    /// the free variables it reaches are the same, as for path
    /// compression, so it is written as one (see
    /// [`SubstWrite::Compressed`]).
    pub fn link_equal(&mut self, var: TVarName, ty: Type) {
        self.version += 1;
        let ty = Arc::new(ty);
        if self.trail.is_some() {
            let by = &mut self.mentioned_by;
            ty.any_var(&mut |u| {
                let list = by.entry(u.clone()).or_default();
                if list.last() != Some(&var) {
                    list.push(var.clone());
                }
                false
            });
        }
        let prev = self.map.insert(var.clone(), ty);
        if let Some(trail) = self.trail.as_mut() {
            trail.push(match prev {
                Some(prev) => SubstUndo::Compressed(var, prev),
                None => SubstUndo::Type(var, None),
            });
            self.serials.push(self.next_serial);
            self.next_serial += 1;
        }
    }

    /// Insert a type mapping into the substitution.
    pub fn insert(&mut self, var: TVarName, ty: Type) {
        self.write(var, Arc::new(ty));
    }

    /// [`Self::insert`] of a type shared with another table.
    pub fn insert_shared(&mut self, var: TVarName, ty: Arc<Type>) {
        self.write(var, ty);
    }

    /// Insert a presence mapping into the substitution.
    pub fn insert_presence(&mut self, pvar: PVarName, pres: Presence) {
        self.version += 1;
        let prev = self.presences.insert(pvar.clone(), pres);
        if let Some(trail) = self.trail.as_mut() {
            trail.push(SubstUndo::Presence(pvar, prev));
            self.serials.push(self.next_serial);
            self.next_serial += 1;
        }
    }

    /// Remove a type variable from the substitution.
    pub fn remove(&mut self, var: &TVarName) {
        self.version += 1;
        let prev = self.map.remove(var);
        if let (Some(trail), Some(prev)) = (self.trail.as_mut(), prev) {
            trail.push(SubstUndo::Type(var.clone(), Some(prev)));
            self.serials.push(self.next_serial);
            self.next_serial += 1;
        }
    }

    /// Get the domain (set of type variables) of this substitution.
    pub fn domain(&self) -> HashSet<TVarName> {
        self.map.keys().cloned().collect()
    }

    /// Get the presence-variable domain.
    pub fn presence_domain(&self) -> HashSet<PVarName> {
        self.presences.keys().cloned().collect()
    }

    /// Resolve a presence chain through the substitution. Returns the
    /// presence concrete or the first unbound variable.
    pub fn resolve_presence(&self, pres: &Presence) -> Presence {
        let mut current = pres.clone();
        let mut visited: HashSet<PVarName> = HashSet::new();
        loop {
            match &current {
                Presence::Pre | Presence::Abs => return current,
                Presence::Var(v) => {
                    if !visited.insert(v.clone()) {
                        return current;
                    }
                    match self.presences.get(v) {
                        Some(next) => current = next.clone(),
                        None => return current,
                    }
                }
            }
        }
    }

    /// Compose two substitutions: (self ∘ other)(x) = self(other(x))
    ///
    /// The result maps each variable to its fully substituted form.
    /// Variables in `other` are mapped through `self`, and variables
    /// only in `self` are kept.
    pub fn compose(&self, other: &Subst) -> Subst {
        let mut result = HashMap::new();

        // Apply self to all mappings in other
        for (var, ty) in &other.map {
            result.insert(var.clone(), Arc::new(self.apply(&**ty)));
        }

        // Add mappings from self that aren't in other
        for (var, ty) in &self.map {
            if !result.contains_key(var) {
                result.insert(var.clone(), ty.clone());
            }
        }

        // Same composition rule on presences. Both maps live in
        // separate namespaces so we never need to thread a presence
        // through a type-map lookup or vice versa.
        let mut presences = HashMap::new();
        for (pvar, pres) in &other.presences {
            presences.insert(pvar.clone(), self.apply_presence(pres));
        }
        for (pvar, pres) in &self.presences {
            if !presences.contains_key(pvar) {
                presences.insert(pvar.clone(), pres.clone());
            }
        }

        Subst {
            map: result,
            presences,
            trail: None,
            serials: Vec::new(),
            next_serial: 0,
            mentioned_by: HashMap::new(),
            version: 0,
            simultaneous: false,
        }
    }

    /// Apply this substitution to a presence (shallow — one step of
    /// presence-variable resolution).
    pub fn apply_presence(&self, pres: &Presence) -> Presence {
        match pres {
            Presence::Pre | Presence::Abs => pres.clone(),
            Presence::Var(v) => match self.presences.get(v) {
                Some(bound) => bound.clone(),
                None => pres.clone(),
            },
        }
    }

    /// Apply this substitution to a substitutable value.
    pub fn apply<T: Substitutable>(&self, t: &T) -> T {
        t.apply_subst(self)
    }

    /// Create a new substitution with certain variables removed.
    pub fn remove_vars(&self, vars: &[TVarName]) -> Subst {
        let mut map = self.map.clone();
        for var in vars {
            map.remove(var);
        }
        Subst {
            map,
            presences: self.presences.clone(),
            trail: None,
            serials: Vec::new(),
            next_serial: 0,
            mentioned_by: HashMap::new(),
            version: 0,
            simultaneous: false,
        }
    }

    /// Iterate over the mappings.
    pub fn iter(&self) -> impl Iterator<Item = (&TVarName, &Type)> {
        self.map.iter().map(|(v, t)| (v, &**t))
    }

    /// Walk a type and merge every row tail variable that resolves
    /// to a row in this substitution into the row's own props.
    ///
    /// `apply_subst` is intentionally shallow on row tails — it's
    /// called by `Subst::compose` over every existing binding on
    /// every `extend_subst`, so a deep merge there explodes
    /// combinatorially on builder patterns and recursive
    /// `this`-typed rows. The rule it skips ("when `ρ` is bound to
    /// `Row(R)`, replace `RowTail::Open(ρ)` with `R`'s contents")
    /// is needed for two things: the printer's view of a type, and
    /// `generalize`'s computation of free variables. Both are
    /// boundary operations that run once per type, not inside the
    /// inference loop, so we do the merge lazily here.
    ///
    /// Cycles can exist on row tails because `unify_rows` extends
    /// the substitution directly without going through
    /// `var_bind`'s recursive-type wrapping; they are cut where they
    /// close (see `flatten_var`). Every other occurrence of a bound
    /// variable is expanded in full — an earlier version expanded each
    /// variable once per call and left later occurrences as bare
    /// (bound) variables, so a type mentioning the same row twice lost
    /// fields and could get a bound variable quantified.
    pub fn flatten(&self, ty: &Type) -> Type {
        let mut state = FlattenState::default();
        self.flatten_type(ty, &mut state)
    }

    /// [`Self::flatten`] for a printer: once about `budget` nodes have
    /// been written out, a bound variable met after is left out (a
    /// `Named` of [`super::ty::ELIDED_TYPE_ID`], which prints as `…`).
    /// A type that mentions a large one in many places would otherwise be
    /// written out exponentially larger than the substitution holds it.
    pub fn flatten_bounded(&self, ty: &Type, budget: usize) -> Type {
        let mut state = FlattenState {
            budget: Some(budget),
            ..FlattenState::default()
        };
        self.flatten_type(ty, &mut state)
    }

    /// Resolve a variable to its fully flattened binding (or itself when
    /// unbound). Every occurrence of a bound variable is expanded — a type
    /// like `{p: o, q: o}` mentions `o`'s row twice — but each expansion
    /// is computed once and memoised, so the walk stays linear in the size
    /// of the substitution. Cycles (equi-recursive bindings) are cut at the
    /// variable being expanded; an expansion that had to cut one is not
    /// memoised, since it is only valid inside that cycle.
    fn flatten_var(&self, name: &TVarName, state: &mut FlattenState) -> Type {
        // (A row's tail is expanded whatever the budget: it holds the
        // rest of the row's fields, whose types the budget still bounds.)
        let tail = std::mem::take(&mut state.expanding_tail);
        let Some(bound) = self.get(name) else {
            return Type::Var(name.clone());
        };
        if let Some(budget) = state.budget {
            if state.written >= budget && !tail {
                return Type::Named(super::ty::ELIDED_TYPE_ID, Vec::new());
            }
        }
        // A type written out before, if the budget has room for it: it may
        // be far larger (a tree of what the substitution shares). Else a
        // tail, which is written whatever the budget, is written again
        // within it, and any other type is left out.
        let memo = match (state.memo.get(name), state.budget) {
            (Some(done), None) => Some(done.clone()),
            (Some(done), Some(budget)) => {
                let left = budget.saturating_sub(state.written);
                let size = self.flattened_size(done, left.saturating_add(1));
                if size <= left {
                    state.written += size;
                    Some(done.clone())
                } else if tail {
                    None
                } else {
                    state.written = budget;
                    return Type::Named(super::ty::ELIDED_TYPE_ID, Vec::new());
                }
            }
            (None, _) => None,
        };
        if let Some(done) = memo {
            return done;
        }
        if !state.in_progress.insert(name.clone()) {
            state.cuts += 1;
            return Type::Var(name.clone());
        }
        let cuts_before = state.cuts;
        let bound = bound.clone();
        state.tail_row = tail;
        // (A tail bound to another variable: that one is the tail now.)
        if tail && matches!(bound, Type::Var(_)) {
            state.expanding_tail = true;
        }
        let flat = self.flatten_type(&bound, state);
        state.in_progress.remove(name);
        if state.cuts == cuts_before {
            state.memo.insert(name.clone(), flat.clone());
        }
        flat
    }

    fn flatten_type(&self, ty: &Type, state: &mut FlattenState) -> Type {
        // Past the budget, a type is left out whatever it is made of, a
        // bound variable or a record written in place: a type stored once
        // may be written many times over (each cycle cut, not memoised).
        let tail_row = std::mem::take(&mut state.tail_row);
        if let Some(budget) = state.budget {
            if state.written >= budget && !tail_row && !matches!(ty, Type::Var(_))
                && ty.has_parts()
                // (A name alone, `Pane`, is as short as what replaces it.)
                && !matches!(ty, Type::Named(_, args) if args.is_empty())
            {
                return Type::Named(super::ty::ELIDED_TYPE_ID, Vec::new());
            }
        }
        state.written += 1;
        match ty {
            // Resolve variables at any depth, not just the top level —
            // `Subst::compose` only fully applies the substitution to its
            // own keys, so rows bound to rows can still mention bound
            // variables.
            Type::Var(name) => self.flatten_var(name, state),
            Type::Row(row) => Type::Row(self.flatten_row(row, state)),
            Type::Func {
                this_type,
                params,
                ret,
            } => Type::Func {
                this_type: this_type
                    .as_ref()
                    .map(|t| Box::new(self.flatten_type(t, state))),
                params: params
                    .iter()
                    .map(|p| super::ty::FuncParam {
                        presence: self.resolve_presence(&p.presence),
                        ty: self.flatten_type(&p.ty, state),
                        name: p.name.clone(),
                    })
                    .collect(),
                ret: Box::new(self.flatten_type(ret, state)),
            },
            Type::Array(elem) => Type::Array(Box::new(self.flatten_type(elem, state))),
            Type::Maybe(z, elem) => Type::Maybe(*z, Box::new(self.flatten_type(elem, state))),
            Type::Promise(inner) => Type::Promise(Box::new(self.flatten_type(inner, state))),
            Type::Map(value) => Type::Map(Box::new(self.flatten_type(value, state))),
            Type::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| self.flatten_type(e, state)).collect())
            }
            Type::Union(members) => {
                Type::union(members.iter().map(|m| self.flatten_type(m, state)))
            }
            Type::Named(id, args) => Type::Named(
                *id,
                args.iter().map(|a| self.flatten_type(a, state)).collect(),
            ),
            // Module/Literal/primitives: nothing to flatten.
            _ => ty.clone(),
        }
    }

    fn flatten_row(&self, row: &RowType, state: &mut FlattenState) -> RowType {
        let mut props: std::collections::BTreeMap<PropName, FieldEntry> = row
            .props
            .iter()
            .map(|(k, e)| {
                (
                    k.clone(),
                    e.map(
                        &mut |p| self.resolve_presence(p),
                        self.flatten_type(&e.ty, state),
                    ),
                )
            })
            .collect();

        let tail = match &row.tail {
            RowTail::Closed => RowTail::Closed,
            RowTail::Recursive(id, args) => RowTail::Recursive(
                *id,
                args.iter().map(|a| self.flatten_type(a, state)).collect(),
            ),
            // The tail variable's own flattening already merged the rest
            // of its tail chain, so one step suffices. Fields of the row
            // itself take precedence over the tail's.
            RowTail::Open(var) => match {
                state.expanding_tail = true;
                self.flatten_var(var, state)
            } {
                Type::Row(rest) => {
                    for (k, e) in rest.props {
                        props.entry(k).or_insert(e);
                    }
                    rest.tail
                }
                Type::Var(v) => RowTail::Open(v),
                _ => RowTail::Open(var.clone()),
            },
        };

        RowType {
            props: props.into(),
            tail,
        }
    }
}

impl Subst {
    /// How many nodes [`Self::flatten`] would give for `ty`, counted
    /// without building it (each variable's count once), up to `cap`.
    /// `flatten` builds a tree: a type that mentions a large one in many
    /// places (a DOM element's row, in each of its event handlers'
    /// events) expands to far more than the substitution holds, so a
    /// printer asks first.
    pub fn flattened_size(&self, ty: &Type, cap: usize) -> usize {
        let mut state = SizeState::default();
        self.size_of(ty, cap, &mut state)
    }

    fn size_of(&self, ty: &Type, cap: usize, state: &mut SizeState) -> usize {
        let sum = |types: &mut dyn Iterator<Item = &Type>, state: &mut SizeState| {
            let mut n = 1usize;
            for t in types {
                n = n.saturating_add(self.size_of(t, cap, state));
                if n >= cap {
                    return cap;
                }
            }
            n
        };
        match ty {
            Type::Var(name) => self.size_of_var(name, cap, state),
            Type::Row(row) => {
                let mut n = sum(&mut row.props.values().map(|e| &e.ty), state);
                match &row.tail {
                    RowTail::Open(var) => n = n.saturating_add(self.size_of_var(var, cap, state)),
                    RowTail::Recursive(_, args) => {
                        n = n.saturating_add(sum(&mut args.iter(), state))
                    }
                    RowTail::Closed => {}
                }
                n.min(cap)
            }
            Type::Func {
                this_type,
                params,
                ret,
            } => sum(
                &mut this_type
                    .iter()
                    .map(|t| &**t)
                    .chain(params.iter().map(|p| &p.ty))
                    .chain(std::iter::once(&**ret)),
                state,
            ),
            Type::Array(t) | Type::Maybe(_, t) | Type::Promise(t) | Type::Map(t) => {
                sum(&mut std::iter::once(&**t), state)
            }
            Type::Tuple(ts) | Type::Union(ts) | Type::Named(_, ts) => sum(&mut ts.iter(), state),
            _ => 1,
        }
    }

    /// A variable's count, memoised exactly when `flatten` memoises its
    /// expansion: not when the expansion cut a cycle, since `flatten`
    /// then writes it out again at each occurrence (so a type whose
    /// variables mention each other in cycles, as DOM elements chained
    /// through `appendChild` do, is counted as large as `flatten` makes
    /// it, rather than as the substitution holds it).
    fn size_of_var(&self, name: &TVarName, cap: usize, state: &mut SizeState) -> usize {
        let Some(bound) = self.get(name) else {
            return 1;
        };
        if let Some(&n) = state.memo.get(name) {
            return n;
        }
        // A cycle is cut where it closes, as `flatten` cuts it.
        if !state.in_progress.insert(name.clone()) {
            state.cuts += 1;
            return 1;
        }
        let cuts_before = state.cuts;
        let n = self.size_of(bound, cap, state);
        state.in_progress.remove(name);
        if state.cuts == cuts_before {
            state.memo.insert(name.clone(), n);
        }
        n
    }
}

/// [`Subst::flattened_size`]'s walk: as [`FlattenState`], counting.
#[derive(Default)]
struct SizeState {
    in_progress: HashSet<TVarName>,
    memo: HashMap<TVarName, usize>,
    cuts: usize,
}

/// What a type reaches through a substitution: the free type and
/// presence variables and the named types (see [`Subst::reach`]).
#[derive(Default, Debug, Clone)]
pub struct Reach {
    pub vars: HashSet<TVarName>,
    pub pvars: HashSet<PVarName>,
    pub named: HashSet<super::TypeId>,
}

#[cfg(test)]
impl Reach {
    fn extend_from(&mut self, other: &Reach) {
        self.vars.extend(other.vars.iter().cloned());
        self.pvars.extend(other.pvars.iter().cloned());
        self.named.extend(other.named.iter().copied());
    }
}

/// The state of a walk shared by several [`Subst::reach_in`] calls.
#[derive(Default, Debug)]
pub struct ReachWalk {
    /// Bound variables whose bindings have been gone through, each with
    /// the layer that went through it: what it reaches is in that
    /// layer's reach or a lower one's.
    done: HashMap<TVarName, usize>,
    /// The layer being walked: a variable a higher layer went through is
    /// gone through again (so that layer can be forgotten).
    level: usize,
    /// The variables each layer went through (some since gone through
    /// again by a lower one).
    owned: Vec<Vec<TVarName>>,
    /// Tarjan's search for the cycles of bindings (strongly connected
    /// components): each bound variable being gone through, by the order
    /// it was met in; the ones whose component isn't finished, in that
    /// order; for each binding being gone through, the earliest of those
    /// it reaches; and the variables a binding reached while they were
    /// being gone through (one bound to a type holding itself).
    index: HashMap<TVarName, usize>,
    stack: Vec<TVarName>,
    lows: Vec<usize>,
    met_again: HashSet<TVarName>,
    next_index: usize,
    /// The last call met a variable an earlier call went through.
    pub skipped: bool,
}

impl ReachWalk {
    /// Walk as layer `level` from now on.
    pub fn set_level(&mut self, level: usize) {
        self.level = level;
    }

    /// Forget what the layers from `level` up went through.
    pub fn forget_from(&mut self, level: usize) {
        while self.owned.len() > level {
            let gone = self.owned.len() - 1;
            for v in self.owned.pop().expect("a layer") {
                if self.done.get(&v) == Some(&gone) {
                    self.done.remove(&v);
                }
            }
        }
        self.level = self.level.min(level);
    }

    /// Record that the current layer went through what `other` (a walk of
    /// its own) went through.
    fn absorb(&mut self, other: ReachWalk) {
        if self.owned.len() <= self.level {
            self.owned.resize_with(self.level + 1, Vec::new);
        }
        for (v, _) in other.done {
            if self.done.get(&v).is_none_or(|&l| l > self.level) {
                self.done.insert(v.clone(), self.level);
                self.owned[self.level].push(v);
            }
        }
    }

    /// Whether this walk went through `var`'s binding (in any layer).
    pub fn went_through(&self, var: &TVarName) -> bool {
        self.done.contains_key(var)
    }
}

impl Subst {
    /// The free type and presence variables, and the named type ids, that
    /// `ty` reaches through the substitution, found without building its
    /// flattened type: each bound variable's binding is walked once. (A
    /// flattened type is a tree, exponentially larger than the
    /// substitution when it mentions a large type in many places; a
    /// caller that only wants these sets shouldn't build it.)
    ///
    /// Every binding met is gone through (a row tail bound to a type that
    /// isn't a row, a module's variables too). Listed are the free
    /// variables met, and the bound ones on a cycle of bindings: all of a
    /// cycle's, as `flatten` keeps a variable where it cuts one, and which
    /// it cuts depends on where it enters. So what is listed depends only
    /// on the substitution, not on the order of a walk or of the walks a
    /// [`ReachWalk`] shares.
    pub fn reach(&self, ty: &Type, into: &mut Reach) {
        self.reach_in(ty, into, &mut ReachWalk::default());
    }

    /// [`Self::reach`], on a walk of its own, what it went through then
    /// recorded in `walk`'s current layer: for a type whose bindings may
    /// close a cycle through ones `walk` went through (and so skips, not
    /// seeing the cycle).
    pub fn reach_afresh_in(&self, ty: &Type, into: &mut Reach, walk: &mut ReachWalk) {
        let mut own = ReachWalk::default();
        self.reach_type(ty, into, &mut own);
        walk.absorb(own);
    }

    /// [`Self::reach`], as part of `walk`: a bound variable an earlier
    /// call in the same walk went through is not gone through again (what
    /// it reaches is in that call's [`Reach`]). For callers that only
    /// want the union of several types' reaches; `walk.skipped` tells
    /// whether this call's `Reach` may be missing what such a variable
    /// reaches.
    pub fn reach_in(&self, ty: &Type, into: &mut Reach, walk: &mut ReachWalk) {
        walk.skipped = false;
        self.reach_type(ty, into, walk);
    }

    fn reach_var(&self, name: &TVarName, into: &mut Reach, walk: &mut ReachWalk) {
        let Some(bound) = self.get(name) else {
            into.vars.insert(name.clone());
            return;
        };
        // Being gone through: a cycle of bindings, closed here.
        if let Some(&i) = walk.index.get(name) {
            if let Some(low) = walk.lows.last_mut() {
                *low = (*low).min(i);
            }
            walk.met_again.insert(name.clone());
            return;
        }
        if walk.done.get(name).is_some_and(|&l| l <= walk.level) {
            walk.skipped = true;
            return;
        }
        let i = walk.next_index;
        walk.next_index += 1;
        walk.index.insert(name.clone(), i);
        walk.stack.push(name.clone());
        walk.lows.push(i);
        self.reach_type(bound, into, walk);
        let low = walk.lows.pop().expect("this variable's");
        if let Some(outer) = walk.lows.last_mut() {
            *outer = (*outer).min(low);
        }
        if low < i {
            // Part of a cycle through a variable met before: finished
            // with it.
            return;
        }
        // The variables of this one's component, all gone through now. A
        // bound variable on a cycle stays in `flatten`'s output (where it
        // cuts the cycle), so the cycle's variables are reached: all of
        // them, wherever a walk enters the cycle.
        let at = walk
            .stack
            .iter()
            .rposition(|v| v == name)
            .expect("on the stack");
        let component: Vec<TVarName> = walk.stack.drain(at..).collect();
        let cyclic = component.len() > 1 || walk.met_again.contains(name);
        if walk.owned.len() <= walk.level {
            walk.owned.resize_with(walk.level + 1, Vec::new);
        }
        for v in component {
            walk.index.remove(&v);
            walk.met_again.remove(&v);
            walk.done.insert(v.clone(), walk.level);
            walk.owned[walk.level].push(v.clone());
            if cyclic {
                into.vars.insert(v);
            }
        }
    }

    /// What presence `p` resolves to, if a variable, into `into`.
    pub fn reach_presence_var(&self, p: &PVarName, into: &mut Reach) {
        self.reach_presence(&Presence::Var(p.clone()), into);
    }

    fn reach_presence(&self, p: &Presence, into: &mut Reach) {
        // (A chain of presence bindings that cycles ends at a bound one,
        // which isn't free.)
        if let Presence::Var(v) = self.resolve_presence(p) {
            if !self.presences.contains_key(&v) {
                into.pvars.insert(v);
            }
        }
    }

    fn reach_type(&self, ty: &Type, into: &mut Reach, walk: &mut ReachWalk) {
        match ty {
            Type::Var(name) => self.reach_var(name, into, walk),
            Type::Row(row) => {
                for e in row.props.values() {
                    for p in e.presences() {
                        self.reach_presence(p, into);
                    }
                    self.reach_type(&e.ty, into, walk);
                }
                match &row.tail {
                    RowTail::Closed => {}
                    RowTail::Recursive(id, args) => {
                        into.named.insert(*id);
                        for a in args {
                            self.reach_type(a, into, walk);
                        }
                    }
                    RowTail::Open(var) => self.reach_var(var, into, walk),
                }
            }
            Type::Func {
                this_type,
                params,
                ret,
            } => {
                if let Some(t) = this_type {
                    self.reach_type(t, into, walk);
                }
                for p in params {
                    self.reach_presence(&p.presence, into);
                    self.reach_type(&p.ty, into, walk);
                }
                self.reach_type(ret, into, walk);
            }
            Type::Array(t) | Type::Maybe(_, t) | Type::Promise(t) | Type::Map(t) => {
                self.reach_type(t, into, walk)
            }
            Type::Tuple(ts) | Type::Union(ts) => {
                for t in ts {
                    self.reach_type(t, into, walk);
                }
            }
            Type::Named(id, args) => {
                into.named.insert(*id);
                for a in args {
                    self.reach_type(a, into, walk);
                }
            }
            // `flatten` leaves a module as it is.
            // A module's exports' free variables, through the substitution
            // as any other.
            Type::Module(_) => {
                for v in ty.free_vars() {
                    self.reach_var(&v, into, walk);
                }
                for p in ty.free_pvars() {
                    self.reach_presence(&Presence::Var(p), into);
                }
            }
            _ => {}
        }
    }
}

/// Working state of one [`Subst::flatten`] call.
#[derive(Default)]
struct FlattenState {
    /// Variables whose expansion is on the current path (cycle detection).
    in_progress: HashSet<TVarName>,
    /// Finished expansions, reused for every later occurrence.
    memo: HashMap<TVarName, Type>,
    /// Number of cycle cuts so far; see [`Subst::flatten_var`].
    cuts: usize,
    /// Nodes written so far, and how many to write before leaving bound
    /// variables out ([`Subst::flatten_bounded`]).
    written: usize,
    budget: Option<usize>,
    /// The variable about to be expanded is a row's tail.
    expanding_tail: bool,
    /// The type about to be written is the row a tail is bound to: written
    /// whatever the budget (its fields' types aren't).
    tail_row: bool,
}

impl IntoIterator for Subst {
    type Item = (TVarName, Type);
    type IntoIter = std::vec::IntoIter<(TVarName, Type)>;

    fn into_iter(self) -> Self::IntoIter {
        self.map
            .into_iter()
            .map(|(v, t)| (v, Arc::unwrap_or_clone(t)))
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl FromIterator<(TVarName, Type)> for Subst {
    fn from_iter<T: IntoIterator<Item = (TVarName, Type)>>(iter: T) -> Self {
        Subst {
            map: iter.into_iter().map(|(v, t)| (v, Arc::new(t))).collect(),
            presences: HashMap::new(),
            trail: None,
            serials: Vec::new(),
            next_serial: 0,
            mentioned_by: HashMap::new(),
            version: 0,
            simultaneous: false,
        }
    }
}

/// Trait for types that can have substitutions applied.
pub trait Substitutable {
    /// Apply a substitution to this value.
    fn apply_subst(&self, subst: &Subst) -> Self;

    /// Collect all free type variables.
    fn free_vars(&self) -> HashSet<TVarName>;
}

impl Substitutable for Type {
    fn apply_subst(&self, subst: &Subst) -> Self {
        // Bail to `Type::Error` past the depth limit. `Type::Error`
        // is the existing best-effort recovery sentinel (it unifies
        // trivially and absorbs downstream operations), so a deep
        // walk that hits the cap degrades gracefully instead of
        // overflowing the stack. The driver picks up the flag and
        // emits a diagnostic; see `docs/scaling.md`.
        let Some(_guard) = ApplySubstGuard::try_enter() else {
            return Type::Error;
        };
        match self {
            // Primitives are unchanged
            Type::Number => Type::Number,
            Type::String => Type::String,
            Type::Boolean => Type::Boolean,
            Type::Undefined => Type::Undefined,
            Type::Null => Type::Null,
            Type::Regex => Type::Regex,
            Type::NewTarget => Type::NewTarget,
            Type::ArrowThis => Type::ArrowThis,
            Type::TypedArray(k) => Type::TypedArray(*k),

            // Variable substitution
            Type::Var(name) => {
                if let Some(ty) = subst.get(name) {
                    if subst.simultaneous {
                        return ty.clone();
                    }
                    // Recursively apply to handle transitive substitutions
                    ty.apply_subst(subst)
                } else {
                    self.clone()
                }
            }

            // Function types
            Type::Func {
                this_type,
                params,
                ret,
            } => Type::Func {
                this_type: this_type.as_ref().map(|t| Box::new(t.apply_subst(subst))),
                params: params
                    .iter()
                    .map(|p| super::ty::FuncParam {
                        presence: subst.apply_presence(&p.presence),
                        ty: p.ty.apply_subst(subst),
                        name: p.name.clone(),
                    })
                    .collect(),
                ret: Box::new(ret.apply_subst(subst)),
            },

            // Row types
            Type::Row(row) => Type::Row(row.apply_subst(subst)),

            // Array types
            Type::Array(elem) => Type::Array(Box::new(elem.apply_subst(subst))),
            Type::Maybe(z, elem) => Type::Maybe(*z, Box::new(elem.apply_subst(subst))),

            // Promise types
            Type::Promise(inner) => Type::Promise(Box::new(inner.apply_subst(subst))),

            // Map types
            Type::Map(value) => Type::Map(Box::new(value.apply_subst(subst))),

            // Tuple types — substitute each component.
            Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| e.apply_subst(subst)).collect()),

            // Named recursive types
            Type::Named(id, args) => {
                Type::Named(*id, args.iter().map(|a| a.apply_subst(subst)).collect())
            }

            // Literal types are unchanged by substitution
            Type::Literal(lit) => Type::Literal(lit.clone()),

            // Substitution can produce duplicates / nested unions, so
            // re-normalise via Type::union.
            Type::Union(members) => Type::union(members.iter().map(|m| m.apply_subst(subst))),

            // Modules: each export is a scheme; reuse TypeScheme's
            // substitution which already shadows quantified vars.
            Type::Module(m) => Type::Module(crate::types::ModuleType {
                source: m.source.clone(),
                exports: m
                    .exports
                    .iter()
                    .map(|(k, scheme)| (k.clone(), scheme.apply_subst(subst)))
                    .collect(),
            }),

            // Error sentinel: substitution is the identity. The
            // binding already failed; nothing here can change.
            Type::Error => Type::Error,
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        Type::free_vars(self)
    }
}

impl Substitutable for RowType {
    fn apply_subst(&self, subst: &Subst) -> Self {
        // `apply_subst` stays shallow on purpose: it's invoked
        // implicitly by `Subst::compose` on every existing binding
        // every time a new binding is added during inference, so
        // any deep work here amplifies into N² behaviour through
        // the chained-method / builder shape. The full row-tail
        // merge that Rémy unification's substitution semantics
        // require is implemented by `Subst::flatten` and called
        // only at the boundaries that need it (pretty-printing,
        // generalisation).
        let props: std::collections::BTreeMap<PropName, FieldEntry> = self
            .props
            .iter()
            .map(|(k, e)| (k.clone(), e.apply_subst(subst)))
            .collect();

        let tail = match &self.tail {
            RowTail::Closed => RowTail::Closed,
            RowTail::Open(var) => match subst.get(var) {
                Some(Type::Var(new_var)) => RowTail::Open(new_var.clone()),
                _ => RowTail::Open(var.clone()),
            },
            RowTail::Recursive(id, args) => {
                RowTail::Recursive(*id, args.iter().map(|a| a.apply_subst(subst)).collect())
            }
        };

        RowType {
            props: props.into(),
            tail,
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for entry in self.props.values() {
            vars.extend(entry.free_vars());
        }
        match &self.tail {
            RowTail::Open(var) => {
                vars.insert(var.clone());
            }
            RowTail::Recursive(_, args) => {
                for arg in args {
                    vars.extend(arg.free_vars());
                }
            }
            RowTail::Closed => {}
        }
        vars
    }
}

impl Substitutable for FieldEntry {
    fn apply_subst(&self, subst: &Subst) -> Self {
        self.map(&mut |p| subst.apply_presence(p), self.ty.apply_subst(subst))
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        self.ty.free_vars()
    }
}

impl Substitutable for TypePred {
    fn apply_subst(&self, subst: &Subst) -> Self {
        TypePred {
            class: self.class,
            types: self.types.iter().map(|t| t.apply_subst(subst)).collect(),
            origin: self.origin,
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for ty in &self.types {
            vars.extend(ty.free_vars());
        }
        vars
    }
}

impl Substitutable for QualType {
    fn apply_subst(&self, subst: &Subst) -> Self {
        QualType {
            preds: self.preds.iter().map(|p| p.apply_subst(subst)).collect(),
            ty: self.ty.apply_subst(subst),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.ty.free_vars();
        for pred in &self.preds {
            vars.extend(pred.free_vars());
        }
        vars
    }
}

impl Substitutable for TypeScheme {
    fn apply_subst(&self, subst: &Subst) -> Self {
        // Remove quantified type variables from substitution. We
        // don't need to filter presence variables similarly: a
        // generalized pvar in `self.pvars` couldn't be bound in the
        // outer substitution unless it had leaked, which the
        // env-difference rule in `generalize` prevents.
        let filtered_subst = subst.remove_vars(&self.vars);
        TypeScheme {
            vars: self.vars.clone(),
            pvars: self.pvars.clone(),
            body: self.body.apply_subst(&filtered_subst),
        }
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = self.body.free_vars();
        for v in &self.vars {
            vars.remove(v);
        }
        vars
    }
}

impl<T: Substitutable> Substitutable for Vec<T> {
    fn apply_subst(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply_subst(subst)).collect()
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        let mut vars = HashSet::new();
        for t in self {
            vars.extend(t.free_vars());
        }
        vars
    }
}

impl<T: Substitutable> Substitutable for Option<T> {
    fn apply_subst(&self, subst: &Subst) -> Self {
        self.as_ref().map(|t| t.apply_subst(subst))
    }

    fn free_vars(&self) -> HashSet<TVarName> {
        self.as_ref().map(|t| t.free_vars()).unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_subst() {
        let subst = Subst::empty();
        assert!(subst.is_empty());

        let ty = Type::flex(0);
        assert_eq!(subst.apply(&ty), ty);
    }

    #[test]
    fn test_singleton_subst() {
        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let ty = Type::flex(0);
        assert_eq!(subst.apply(&ty), Type::Number);
    }

    #[test]
    fn test_subst_preserves_other_vars() {
        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let ty = Type::flex(1);
        assert_eq!(subst.apply(&ty), Type::flex(1));
    }

    #[test]
    fn test_subst_in_func() {
        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let ty = Type::simple_func(vec![Type::flex(0)], Type::flex(0));
        let result = subst.apply(&ty);

        assert_eq!(result, Type::simple_func(vec![Type::Number], Type::Number));
    }

    #[test]
    fn test_compose() {
        // s1: a0 -> Number
        // s2: a1 -> a0
        // compose(s1, s2): a0 -> Number, a1 -> Number
        let s1 = Subst::singleton(TVarName::Flex(0), Type::Number);
        let s2 = Subst::singleton(TVarName::Flex(1), Type::flex(0));
        let composed = s1.compose(&s2);

        assert_eq!(composed.apply(&Type::flex(0)), Type::Number);
        assert_eq!(composed.apply(&Type::flex(1)), Type::Number);
    }

    #[test]
    fn test_free_vars() {
        let ty = Type::simple_func(vec![Type::flex(0), Type::flex(1)], Type::Number);
        let vars = ty.free_vars();

        assert!(vars.contains(&TVarName::Flex(0)));
        assert!(vars.contains(&TVarName::Flex(1)));
        assert_eq!(vars.len(), 2);
    }

    #[test]
    fn test_scheme_subst_respects_quantifiers() {
        // forall a0. a0 -> a1
        // Substituting a0 -> Number should only affect a1
        let scheme = TypeScheme::poly(
            vec![TVarName::Flex(0)],
            Type::simple_func(vec![Type::flex(0)], Type::flex(1)),
        );

        let subst = Subst::singleton(TVarName::Flex(0), Type::Number);
        let result = subst.apply(&scheme);

        // The quantified a0 should be unchanged, a1 is not in domain
        assert_eq!(result.vars, vec![TVarName::Flex(0)]);
    }

    /// Build a Type::Array nested `depth` times around `Type::Number`.
    /// Each `Array` layer recurses through `Type::apply_subst`, so this
    /// is a clean knob for exercising the depth limit.
    fn deep_array(depth: usize) -> Type {
        let mut ty = Type::Number;
        for _ in 0..depth {
            ty = Type::Array(Box::new(ty));
        }
        ty
    }

    /// RAII helper for tests that lower the cap. Restores the
    /// previous limit on drop so the rest of the test process keeps
    /// using the default.
    struct DepthLimitScope(usize);
    impl DepthLimitScope {
        fn new(limit: usize) -> Self {
            let prev = set_apply_subst_depth_limit_for_test(limit);
            Self(prev)
        }
    }
    impl Drop for DepthLimitScope {
        fn drop(&mut self) {
            set_apply_subst_depth_limit_for_test(self.0);
        }
    }

    #[test]
    fn apply_subst_below_limit_is_unchanged() {
        let _scope = DepthLimitScope::new(32);
        let _ = take_apply_subst_overflow(); // clear stale flag
        let ty = deep_array(10);
        let result = Subst::empty().apply(&ty);
        assert_eq!(result, ty);
        assert!(
            !take_apply_subst_overflow(),
            "should not overflow well below the cap"
        );
    }

    #[test]
    fn apply_subst_at_limit_returns_error_and_sets_flag() {
        let _scope = DepthLimitScope::new(32);
        let _ = take_apply_subst_overflow(); // clear stale flag
        let ty = deep_array(64);
        let _result = Subst::empty().apply(&ty);
        assert!(
            take_apply_subst_overflow(),
            "overflow flag must be set past the depth cap"
        );
    }

    /// A simultaneous substitution replaces a variable once: `T ↦ T[]`
    /// applied to `T` is `T[]`, not `T[][]…` until the depth cap (how a
    /// named type's body is unrolled at its own parameter).
    #[test]
    fn simultaneous_substitution_replaces_once() {
        let t = TVarName::Flex(7);
        let mut s = Subst::simultaneous();
        s.insert(t.clone(), Type::array(Type::Var(t.clone())));
        let _ = take_apply_subst_overflow();
        assert_eq!(
            s.apply(&Type::Var(t.clone())),
            Type::array(Type::Var(t.clone()))
        );
        assert!(!take_apply_subst_overflow());
    }

    #[test]
    fn apply_subst_overflow_flag_clears_after_read() {
        let _scope = DepthLimitScope::new(32);
        let _ = take_apply_subst_overflow();
        let ty = deep_array(64);
        let _ = Subst::empty().apply(&ty);
        assert!(take_apply_subst_overflow());
        // Second read is now false.
        assert!(!take_apply_subst_overflow());
    }

    #[test]
    fn apply_subst_depth_resets_between_runs() {
        // The depth counter must come back to 0 after a run, so the
        // next call starts fresh. We exercise this by running an
        // overflowing walk and then a shallow one: if the counter
        // leaked, the shallow walk would also see the cap.
        let _scope = DepthLimitScope::new(32);
        let _ = take_apply_subst_overflow();
        let _ = Subst::empty().apply(&deep_array(64));
        let _ = take_apply_subst_overflow(); // clear

        let shallow = Subst::empty().apply(&deep_array(10));
        assert_eq!(shallow, deep_array(10));
        assert!(
            !take_apply_subst_overflow(),
            "shallow walk after overflow must not retrigger"
        );
    }

    // --- Subst::resolve (Tarjan path compression) -----------------
    //
    // These tests pin the observable behaviour of `resolve`:
    //
    //   1. **Endpoint correctness.** A chain α → β → γ → t resolves
    //      to `t` (the chain's first non-`Var` endpoint), or to a
    //      `Type::Var(root)` if the chain ends at an unbound root.
    //   2. **Idempotence.** Calling `resolve(k)` twice returns the
    //      same value, and the second call performs no rewrites
    //      (because the first one already compressed the path).
    //   3. **`apply` invariance.** Resolving a path doesn't change
    //      what `apply` produces for any type — only how cheaply it
    //      gets there. This is the key invariant that justifies
    //      destructive substitution: if `resolve` ever produced a
    //      different `apply` result, we'd silently observe wrong
    //      types downstream.
    //   4. **Cycle safety.** A malformed substitution with a Var
    //      cycle (occurs-check should have prevented it, but the
    //      data structure doesn't enforce that) must not loop.

    fn flex(id: u32) -> TVarName {
        TVarName::Flex(id)
    }

    #[test]
    fn resolve_returns_chain_endpoint() {
        // α → β → γ → Number
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Var(flex(1)));
        s.insert(flex(1), Type::Var(flex(2)));
        s.insert(flex(2), Type::Number);

        assert_eq!(s.resolve(&flex(0)).as_deref().cloned(), Some(Type::Number));
    }

    #[test]
    fn resolve_returns_unbound_root_var() {
        // α → β  (β unbound)
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Var(flex(1)));

        assert_eq!(
            s.resolve(&flex(0)).as_deref().cloned(),
            Some(Type::Var(flex(1)))
        );
        // The unbound endpoint must not be in the map afterwards
        // (path compression writes through every entry on the chain,
        // but stops at the endpoint).
        assert!(!s.map.contains_key(&flex(1)));
    }

    #[test]
    fn resolve_compresses_chain() {
        // α → β → γ → Number; after resolving α once, every
        // intermediate entry now points directly at Number.
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Var(flex(1)));
        s.insert(flex(1), Type::Var(flex(2)));
        s.insert(flex(2), Type::Number);

        let _ = s.resolve(&flex(0)).as_deref().cloned();

        assert_eq!(s.get(&flex(0)), Some(&Type::Number));
        assert_eq!(s.get(&flex(1)), Some(&Type::Number));
        assert_eq!(s.get(&flex(2)), Some(&Type::Number));
    }

    #[test]
    fn resolve_is_idempotent() {
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Var(flex(1)));
        s.insert(flex(1), Type::Var(flex(2)));
        s.insert(flex(2), Type::String);

        let first = s.resolve(&flex(0)).as_deref().cloned();
        let snapshot = s.map.clone();
        let second = s.resolve(&flex(0)).as_deref().cloned();

        assert_eq!(first, second);
        // The second call should be a no-op on the storage: every
        // entry on the chain already points at the endpoint.
        assert_eq!(s.map, snapshot);
    }

    #[test]
    fn resolve_preserves_apply_behaviour() {
        // The whole point of destructive path compression is that
        // `apply` is unchanged. Build a chain, snapshot `apply`
        // results for several types, run `resolve` on each chain
        // variable, then assert the post-resolve `apply` still
        // produces the same output.
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Var(flex(1)));
        s.insert(flex(1), Type::Var(flex(2)));
        s.insert(flex(2), Type::Number);
        s.insert(flex(3), Type::Var(flex(0))); // chain into chain
        s.insert(flex(4), Type::Var(flex(3)));

        let test_types = [
            Type::Var(flex(0)),
            Type::Var(flex(3)),
            Type::Var(flex(4)),
            Type::Array(Box::new(Type::Var(flex(2)))),
            Type::simple_func(vec![Type::Var(flex(1))], Type::Var(flex(4))),
        ];
        let before: Vec<Type> = test_types.iter().map(|t| s.apply(t)).collect();

        for id in 0..=4 {
            let _ = s.resolve(&flex(id)).as_deref().cloned();
        }

        let after: Vec<Type> = test_types.iter().map(|t| s.apply(t)).collect();
        assert_eq!(before, after, "resolve changed apply's output");
    }

    #[test]
    fn resolve_breaks_cycles_defensively() {
        // Malformed substitution with a Var cycle. occurs-check is
        // supposed to prevent this, but the data structure doesn't
        // enforce it — so resolve must not loop.
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Var(flex(1)));
        s.insert(flex(1), Type::Var(flex(2)));
        s.insert(flex(2), Type::Var(flex(0))); // closes the cycle

        let result = s.resolve(&flex(0)).as_deref().cloned();
        // We don't pin the exact return value (any of the three vars
        // is acceptable). Just that the call terminates.
        assert!(matches!(result, Some(Type::Var(_))));
    }

    #[test]
    fn resolve_returns_none_for_unbound() {
        let mut s = Subst::empty();
        s.insert(flex(0), Type::Number);
        assert_eq!(s.resolve(&flex(99)).as_deref().cloned(), None);
    }
}

#[cfg(test)]
mod flatten_budget_tests {
    use super::*;

    /// A type that shares its parts (`x0 = {a: x1, b: x1}`, `x1 = {a: x2,
    /// b: x2}`, …) is exponentially large written out as a tree: a bounded
    /// flattening writes no more than its budget, however it is reached
    /// (it used to write a memoised part whole, and a record stored in
    /// place whatever the budget).
    #[test]
    fn a_bounded_flattening_stays_within_its_budget() {
        // (The last one leads back to the first: each expansion cuts the
        // cycle, so none is memoised.)
        // Its size as written (variables left as they are).
        fn nodes(t: &Type) -> usize {
            match t {
                Type::Row(r) => 1 + r.props.values().map(|e| nodes(&e.ty)).sum::<usize>(),
                _ => 1,
            }
        }
        for cyclic in [false, true] {
            let mut subst = Subst::empty();
            let depth = 40u32;
            for i in 0..depth {
                let next = if cyclic { (i + 1) % depth } else { i + 1 };
                let next = Type::Var(TVarName::Flex(next));
                let row = Type::object([("a", next.clone()), ("b", next)]);
                subst.insert(TVarName::Flex(i), row);
            }
            let flat = subst.flatten_bounded(&Type::Var(TVarName::Flex(0)), 4_000);
            assert!(nodes(&flat) < 20_000, "{}", nodes(&flat));
        }
    }
}

#[cfg(test)]
mod reach_tests {
    use super::*;
    use crate::types::TVarId;
    use std::collections::BTreeMap;

    fn row(fields: &[(&str, Type)], tail: Option<TVarName>) -> Type {
        let props: BTreeMap<PropName, Type> = fields
            .iter()
            .map(|(k, t)| (PropName(k.to_string()), t.clone()))
            .collect();
        Type::Row(match tail {
            Some(v) => RowType::open(props, v),
            None => RowType::closed(props),
        })
    }

    fn vars(r: &Reach) -> Vec<TVarId> {
        let mut v: Vec<TVarId> = r.vars.iter().map(|v| v.id()).collect();
        v.sort();
        v
    }

    /// A cycle of bindings (`a = {f: b}`, `b = {g: a, h: c}`, as type
    /// variables 1, 2 and 3): what it reaches is its free variable and
    /// all of its bound ones, wherever a walk enters it, and whatever walks
    /// shared the walk before. (One walk alone cuts it at the variable it
    /// entered by.)
    #[test]
    fn a_cycle_reaches_the_same_from_any_entry() {
        let mut s = Subst::with_trail();
        s.insert(TVarName::Flex(1), row(&[("f", Type::flex(2))], None));
        s.insert(
            TVarName::Flex(2),
            row(&[("g", Type::flex(1)), ("h", Type::flex(3))], None),
        );
        for entry in [1, 2] {
            let mut r = Reach::default();
            s.reach(&Type::flex(entry), &mut r);
            assert_eq!(vars(&r), vec![1, 2, 3], "entered at {entry}");
        }
        for order in [[1, 2], [2, 1]] {
            let mut walk = ReachWalk::default();
            let mut all = Reach::default();
            for entry in order {
                let mut r = Reach::default();
                s.reach_in(&Type::flex(entry), &mut r, &mut walk);
                all.extend_from(&r);
            }
            assert_eq!(vars(&all), vec![1, 2, 3], "order {order:?}");
        }
        // A variable on a path into the cycle, not on it, isn't listed.
        s.insert(TVarName::Flex(4), row(&[("p", Type::flex(1))], None));
        let mut r = Reach::default();
        s.reach(&Type::flex(4), &mut r);
        assert_eq!(vars(&r), vec![1, 2, 3]);
    }

    /// A variable bound to a type holding itself is a cycle of one.
    #[test]
    fn a_variable_bound_to_a_type_holding_itself_is_listed() {
        let mut s = Subst::with_trail();
        s.insert(
            TVarName::Flex(1),
            row(&[("f", Type::flex(1))], Some(TVarName::Flex(2))),
        );
        let mut r = Reach::default();
        s.reach(&Type::flex(1), &mut r);
        assert_eq!(vars(&r), vec![1, 2]);
    }

    /// A row tail bound to a type that isn't a row: what that type
    /// reaches is reached, not the tail itself.
    #[test]
    fn a_tail_bound_to_another_type_is_gone_through() {
        let mut s = Subst::with_trail();
        s.insert(
            TVarName::Flex(1),
            Type::func(Type::Undefined, vec![Type::flex(2)], Type::Number),
        );
        let ty = row(&[("x", Type::Number)], Some(TVarName::Flex(1)));
        let mut r = Reach::default();
        s.reach(&ty, &mut r);
        assert_eq!(vars(&r), vec![2]);
    }
}
