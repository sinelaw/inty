import Inty.Rigid

/-!
# Rigid variables in a type's tree

Equal types can differ in their rigid variables, as in their type variables,
where a recursive type's system has an equation its unfolding never reaches.
`Ty.TreeRk k τ`: the rigid variable `k` is a leaf of the tree `τ` unfolds to,
which equal types agree on; `Ty.trk` computes them, for inference's check
that a polymorphic annotation's rigid variables don't escape.
-/

namespace Inty

/-- The rigid variable `k`, applied to nothing, is a leaf of a finite tree. -/
inductive Tree.HasRk (k : Nat) : Tree → Prop
  | here {c : Con} {ts : List Tree} : k ∈ c.rkeys → ts = [] → Tree.HasRk k (.node c ts)
  | under {c : Con} {ts : List Tree} {t : Tree} : t ∈ ts → Tree.HasRk k t →
      Tree.HasRk k (.node c ts)

/-- `k` is a leaf of the tree `τ` unfolds to. -/
def Ty.TreeRk (k : Nat) (τ : Ty) : Prop := ∃ n, (τ.approx n).HasRk k

theorem TyEq.treeRk {s t : Ty} (h : TyEq s t) {k : Nat} (hs : s.TreeRk k) : t.TreeRk k := by
  obtain ⟨n, hn⟩ := hs; exact ⟨n, h n ▸ hn⟩

theorem RTy.rkeys_open {env : Nat → Ty} {K : List Nat} (henv : ∀ j, ∀ x ∈ (env j).rkeys, x ∈ K) :
    ∀ (r : RTy), (∀ x ∈ r.rkeys, x ∈ K) → ∀ x ∈ (r.open env).rkeys, x ∈ K := by
  intro r
  induction r using RTy.ind with
  | free a => simp [RTy.open, Ty.rkeys]
  | self j => intro _; exact henv j
  | app c args ih =>
    intro hr x hx
    simp only [RTy.open_app, Ty.rkeys, Ty.rkeysL_eq, List.flatMap_map, List.mem_append,
      List.mem_flatMap] at hx
    simp only [RTy.rkeys, RTy.rkeysL_eq, List.mem_append, List.mem_flatMap] at hr
    rcases hx with hx | ⟨p, hp, hx⟩
    · exact hr x (.inl hx)
    · exact ih p hp (fun y hy => hr y (.inr ⟨p, hp, hy⟩)) x hx
  | mu i sys _ => intro hr x hx; exact hr x (by simpa [RTy.open, Ty.rkeys, RTy.rkeys] using hx)

theorem RTy.rkeys_head : ∀ (r : RTy) {env : Nat → Ty} {K : List Nat} {t : Ty},
    (∀ j, ∀ x ∈ (env j).rkeys, x ∈ K) → (∀ x ∈ r.rkeys, x ∈ K) → RTy.head env r = some t →
    ∀ x ∈ t.rkeys, x ∈ K := by
  intro r
  induction r using RTy.ind with
  | free a => intro env K t _ _ h; simp [RTy.head] at h; subst h; simp [Ty.rkeys]
  | self j => intro env K t _ _ h; simp [RTy.head] at h
  | app c args _ =>
    intro env K t henv hr h
    simp only [RTy.head, Option.some.injEq] at h; subst h
    have := RTy.rkeys_open henv (.app c args) hr
    simpa [RTy.open] using this
  | mu i sys ih =>
    intro env K t _ hr h
    rw [RTy.head] at h
    split at h
    · rename_i r' hr'
      have hm := List.mem_of_getElem? hr'
      refine ih r' hm (fun j x hx => hr x ?_) (fun x hx => hr x ?_) h
      · simpa [muEnv, Ty.rkeys, RTy.rkeys] using hx
      · simp only [RTy.rkeys, RTy.rkeysL_eq, List.mem_flatMap]; exact ⟨r', hm, hx⟩
    · cases h

theorem Ty.rkeys_view {τ t : Ty} (h : τ.view = some t) : ∀ x ∈ t.rkeys, x ∈ τ.rkeys := by
  cases τ with
  | var a => simp [Ty.view] at h; subst h; simp [Ty.rkeys]
  | app c args => simp [Ty.view] at h; subst h; exact fun _ hx => hx
  | mu i sys =>
    simp only [Ty.view, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    have hm := List.mem_of_getElem? hr
    refine RTy.rkeys_head r (fun j x hx => ?_) (fun x hx => ?_) h
    · simpa [muEnv, Ty.rkeys] using hx
    · simp only [Ty.rkeys, RTy.rkeysL_eq, List.mem_flatMap]; exact ⟨r, hm, hx⟩

/-- A leaf of a type's tree is one of its rigid variables. -/
theorem Ty.treeRk_rkeys {k : Nat} : ∀ {n : Nat} {τ : Ty}, (τ.approx n).HasRk k → k ∈ τ.rkeys
  | 0, _, h => by cases h
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h
    split at h
    · cases h
    · rename_i c args hv
      have hv' := Ty.rkeys_view hv
      cases h with
      | here hk _ => exact hv' k (by simp [Ty.rkeys, hk])
      | under ht hh =>
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
        exact hv' k (by
          simp only [Ty.rkeys, Ty.rkeysL_eq, List.mem_append, List.mem_flatMap]
          exact .inr ⟨a, ha, Ty.treeRk_rkeys hh⟩)
    · cases h

theorem Ty.TreeRk.rkeys {k : Nat} {τ : Ty} (h : τ.TreeRk k) : k ∈ τ.rkeys :=
  let ⟨_, hn⟩ := h; Ty.treeRk_rkeys hn

theorem Tree.hasRk_graft {k : Nat} (f : Nat → Nat → Tree) :
    ∀ {n : Nat} {τ : Ty}, (τ.approx n).HasRk k → ((τ.approx n).graft f n).HasRk k
  | 0, _, h => by cases h
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h ⊢
    split at h
    · cases h
    · rename_i c args _
      cases h with
      | here hk he =>
        have : args = [] := by simpa using he
        subst this; exact .here hk rfl
      | under ht hh =>
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
        simp only [Tree.graft, List.map_map]
        exact .under (List.mem_map.mpr ⟨a, ha, rfl⟩) (Tree.hasRk_graft f hh)
    · cases h

/-- Substitution keeps a type's rigid leaves. -/
theorem Ty.TreeRk.subst {k : Nat} {τ : Ty} (h : τ.TreeRk k) (σ : Subst) : (τ.subst σ).TreeRk k := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [Ty.approx_subst]; exact Tree.hasRk_graft _ hn⟩

/-! ## Computing them -/

/-- A rigid leaf: a constructor applied to nothing. -/
def Ty.leafRk : Ty → List Nat
  | .app c [] => c.rkeys
  | _ => []

/-- The rigid leaves of a type's tree, computed: those of the nodes it
reaches. -/
def Ty.trk (τ : Ty) : List Nat := τ.reachable.flatMap Ty.leafRk

/-- A kid's rigid leaves are its parent's. -/
theorem Ty.TreeRk.of_kid {x y : Ty} (hy : y ∈ x.kids) {k : Nat} (h : y.TreeRk k) :
    x.TreeRk k := by
  obtain ⟨n, hn⟩ := h
  cases x with
  | var b => simp [Ty.kids] at hy
  | app c args =>
    refine ⟨n + 1, ?_⟩
    simp only [Ty.approx_succ, Ty.view]
    exact .under (List.mem_map_of_mem (by simpa [Ty.kids] using hy)) hn
  | mu i sys =>
    simp only [Ty.kids] at hy
    split at hy
    · rename_i v hv
      simp only [List.mem_singleton] at hy; subst hy
      have hview := Ty.view_whnf (Ty.mu i sys)
      rw [Ty.whnf_of_view hv] at hview
      exact ⟨n, by rw [Ty.approx_congr_view hview.symm]; exact hn⟩
    · cases hy

theorem Ty.Reach.treeRk {τ x : Ty} (h : τ.Reach x) {k : Nat} (hx : x.TreeRk k) :
    τ.TreeRk k := by
  induction h with
  | refl => exact hx
  | step _ hk ih => exact ih (Ty.TreeRk.of_kid hk hx)

theorem Ty.reach_of_hasRk {k : Nat} : ∀ (n : Nat) (τ : Ty), (τ.approx n).HasRk k →
    ∃ c, k ∈ c.rkeys ∧ τ.Reach (.app c [])
  | 0, _, h => by cases h
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h
    cases hv : τ.view with
    | none => rw [hv] at h; cases h
    | some t =>
      rw [hv] at h
      have hr := Ty.reach_view hv
      rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c, args, rfl⟩
      · cases h
      · dsimp only at h
        cases h with
        | here hk he =>
          have : args = [] := by simpa using he
          subst this; exact ⟨c, hk, hr⟩
        | under hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          obtain ⟨c', hk, hr'⟩ := Ty.reach_of_hasRk n x ht
          exact ⟨c', hk, hr.trans ((Ty.Reach.step .refl (by simpa [Ty.kids] using hx)).trans hr')⟩

theorem Ty.mem_trk {τ : Ty} {k : Nat} : k ∈ τ.trk ↔ τ.TreeRk k := by
  rw [Ty.trk, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hk⟩
    refine (Ty.mem_reachable.mp hx).treeRk ?_
    cases x with
    | app c args =>
      cases args with
      | nil =>
        refine ⟨0 + 1, ?_⟩
        simp only [Ty.approx_succ, Ty.view, List.map_nil]
        exact .here (by simpa [Ty.leafRk] using hk) rfl
      | cons => simp [Ty.leafRk] at hk
    | _ => simp [Ty.leafRk] at hk
  · rintro ⟨n, hn⟩
    obtain ⟨c, hk, hr⟩ := Ty.reach_of_hasRk n τ hn
    exact ⟨_, Ty.mem_reachable.mpr hr, by simpa [Ty.leafRk] using hk⟩

end Inty
