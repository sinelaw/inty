import Inty.Unify
import Inty.Classes

/-!
# The variables of a type's unfolding

A recursive type `mu i sys` carries its whole system, and an equation that
its unfolding never reaches may mention variables the type doesn't have:
the unifier's systems have one equation per class of both types, reached
from the root or not. Equal types (`TyEq`) can so differ in their free
variables (`Ty.ftv`), and a substitution of a variable that appears only in
an unreached equation changes the type to an equal one.

The variables that matter are those of the infinite tree a type unfolds
to, its tree variables (`Ty.TV`): equal types have the same ones, and a
substitution changes a type only through them. Generalisation is up to
them (`genVars`): a variable that the environment mentions only in an
unreached equation is not fixed by it. They are computed by a search of the
type's finite graph of subterms (`Ty.tv`).
-/

namespace Inty

/-! ## Tree variables -/

/-- A variable occurring in a tree. -/
inductive Tree.HasVar (a : Nat) : Tree → Prop
  | var : Tree.HasVar a (.var a)
  | node {c : Con} {ts : List Tree} {t : Tree} : t ∈ ts → Tree.HasVar a t →
      Tree.HasVar a (.node c ts)

/-- `a` is a variable of the tree `τ` unfolds to. -/
def Ty.TV (τ : Ty) (a : Nat) : Prop := ∃ n, (τ.approx n).HasVar a

theorem TyEq.tv {s t : Ty} (h : TyEq s t) {a : Nat} : s.TV a ↔ t.TV a :=
  ⟨fun ⟨n, hn⟩ => ⟨n, by rw [← h n]; exact hn⟩, fun ⟨n, hn⟩ => ⟨n, by rw [h n]; exact hn⟩⟩

theorem Ty.approx_zero_hasVar {τ : Ty} {a : Nat} : ¬ (τ.approx 0).HasVar a := fun h => by
  simp only [Ty.approx] at h; cases h

/-- Deeper approximations keep the variables. -/
theorem Ty.approx_hasVar_succ {a : Nat} :
    ∀ (n : Nat) (τ : Ty), (τ.approx n).HasVar a → (τ.approx (n + 1)).HasVar a
  | 0, _, h => absurd h Ty.approx_zero_hasVar
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h ⊢
    cases hv : τ.view with
    | none => rw [hv] at h; cases h
    | some t =>
      rw [hv] at h
      rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c, args, rfl⟩
      · exact h
      · dsimp only at h ⊢
        cases h with
        | node hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          exact .node (List.mem_map_of_mem hx) (Ty.approx_hasVar_succ n x ht)

theorem Ty.approx_hasVar_mono {a : Nat} {τ : Ty} {m : Nat} (h : (τ.approx m).HasVar a) :
    ∀ n, m ≤ n → (τ.approx n).HasVar a := by
  intro n hn
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact h
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact Ty.approx_hasVar_succ n τ (ih (by omega))
    · obtain rfl : m = n + 1 := by omega
      exact h

theorem Ty.TV.of_view_var {τ : Ty} {a : Nat} (h : τ.view = some (.var a)) : τ.TV a :=
  ⟨1, by rw [Ty.approx_succ, h]; exact .var⟩

theorem Ty.TV.of_view_app {τ : Ty} {c : Con} {xs : List Ty} (h : τ.view = some (.app c xs))
    {x : Ty} (hx : x ∈ xs) {a : Nat} (hxa : x.TV a) : τ.TV a := by
  obtain ⟨n, hn⟩ := hxa
  exact ⟨n + 1, by rw [Ty.approx_succ, h]; exact .node (List.mem_map_of_mem hx) hn⟩

theorem Ty.tv_var_self (a : Nat) : (Ty.var a).TV a := Ty.TV.of_view_var rfl

theorem Ty.tv_var {a b : Nat} : (Ty.var a).TV b ↔ b = a := by
  refine ⟨fun ⟨n, hn⟩ => ?_, fun h => h ▸ Ty.tv_var_self a⟩
  cases n with
  | zero => exact absurd hn Ty.approx_zero_hasVar
  | succ n => rw [Ty.approx_succ] at hn; cases hn; rfl

theorem Ty.tv_con {c : Con} {b : Nat} : ¬ (Ty.app c []).TV b := fun ⟨n, hn⟩ => by
  cases n with
  | zero => exact Ty.approx_zero_hasVar hn
  | succ n =>
    rw [Ty.approx_succ] at hn
    cases hn with
    | node hm _ => simp at hm

/-- The variables of a constructor application are its arguments'. -/
theorem Ty.tv_app {c : Con} {xs : List Ty} {a : Nat} :
    (Ty.app c xs).TV a ↔ ∃ x ∈ xs, x.TV a := by
  refine ⟨fun ⟨n, hn⟩ => ?_, fun ⟨x, hx, h⟩ => Ty.TV.of_view_app rfl hx h⟩
  cases n with
  | zero => exact absurd hn Ty.approx_zero_hasVar
  | succ n =>
    rw [Ty.approx_succ] at hn
    cases hn with
    | node hm ht =>
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      exact ⟨x, hx, n, ht⟩

/-- Tree variables are free variables. -/
theorem Ty.TV.ftv {τ : Ty} {a : Nat} (h : τ.TV a) : a ∈ τ.ftv := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing τ with
  | zero => exact absurd hn Ty.approx_zero_hasVar
  | succ n ih =>
    rw [Ty.approx_succ] at hn
    cases hv : τ.view with
    | none => rw [hv] at hn; cases hn
    | some t =>
      rw [hv] at hn
      rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c, args, rfl⟩
      · cases hn; exact Ty.view_ftv hv a (by simp)
      · dsimp only at hn
        cases hn with
        | node hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          exact Ty.view_ftv hv a (by simp only [Ty.ftv_app, List.mem_flatMap]; exact ⟨x, hx, ih ht⟩)

/-! ## Substitution -/

/-- A variable of a variable's image is a variable of the image. -/
theorem Ty.TV.subst_of {σ : Subst} {τ : Ty} {a b : Nat} (ha : τ.TV a)
    (hb : ((Ty.var a).subst σ).TV b) : (τ.subst σ).TV b := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨k, hk⟩ := hb
  refine ⟨n + k, ?_⟩
  induction n generalizing τ with
  | zero => exact absurd hn Ty.approx_zero_hasVar
  | succ n ih =>
    rw [Ty.approx_succ] at hn
    cases hv : τ.view with
    | none => rw [hv] at hn; cases hn
    | some t =>
      rw [hv] at hn
      rcases Ty.view_shape hv with ⟨a', rfl⟩ | ⟨c, args, rfl⟩
      · cases hn
        have hview : (τ.subst σ).view = ((Ty.var a).subst σ).view := by
          rw [Ty.view_subst, hv]; rfl
        rw [Ty.approx_congr_view hview]
        exact Ty.approx_hasVar_mono hk _ (by omega)
      · dsimp only at hn
        cases hn with
        | node hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          rw [show n + 1 + k = (n + k) + 1 by omega, Ty.approx_succ, Ty.view_subst, hv]
          simp only [Option.bind_some, Ty.subst_app, Ty.view, List.map_map]
          exact .node (List.mem_map_of_mem hx) (ih ht)

/-- A variable of an image is one of a variable's image. -/
theorem Ty.TV.subst_inv {σ : Subst} {τ : Ty} {b : Nat} (h : (τ.subst σ).TV b) :
    ∃ a, τ.TV a ∧ ((Ty.var a).subst σ).TV b := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing τ with
  | zero => exact absurd hn Ty.approx_zero_hasVar
  | succ n ih =>
    cases hv : τ.view with
    | none =>
      rw [Ty.approx_succ, Ty.view_subst, hv] at hn; cases hn
    | some t =>
      rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, args, rfl⟩
      · have hview : (τ.subst σ).view = ((Ty.var a).subst σ).view := by
          rw [Ty.view_subst, hv]; rfl
        rw [Ty.approx_congr_view hview] at hn
        exact ⟨a, Ty.TV.of_view_var hv, n + 1, hn⟩
      · rw [Ty.approx_succ, Ty.view_subst, hv] at hn
        simp only [Option.bind_some, Ty.subst_app, Ty.view, List.map_map] at hn
        cases hn with
        | node hm ht =>
          obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
          subst he
          obtain ⟨a, ha, hb⟩ := ih ht
          exact ⟨a, Ty.TV.of_view_app hv hx ha, hb⟩

theorem Ty.tv_subst {σ : Subst} {τ : Ty} {b : Nat} :
    (τ.subst σ).TV b ↔ ∃ a, τ.TV a ∧ ((Ty.var a).subst σ).TV b :=
  ⟨Ty.TV.subst_inv, fun ⟨_, ha, hb⟩ => Ty.TV.subst_of ha hb⟩

/-- Substitutions that give equal types for a type's tree variables give it
equal types. -/
theorem Ty.subst_tyEq_congr_tv {σ σ' : Subst} {τ : Ty}
    (h : ∀ a, τ.TV a → TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    TyEq (τ.subst σ) (τ.subst σ') := by
  refine TyEq.of_bisim (fun x y => ∃ t : Ty, (∀ a, t.TV a → τ.TV a) ∧ x = t.subst σ ∧
    y = t.subst σ') (fun x y hr => ?_) _ _ ⟨τ, fun _ h => h, rfl, rfl⟩
  obtain ⟨t, ht, rfl, rfl⟩ := hr
  cases hv : t.view with
  | none =>
    right
    refine ⟨t.subst σ, t.subst σ', TyEq.refl _, TyEq.refl _, .inl ⟨?_, ?_⟩⟩ <;>
      rw [Ty.view_subst, hv] <;> rfl
  | some v =>
    rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, xs, rfl⟩
    · left
      have hw : TyEq t (.var a) := by
        have := TyEq.whnf t; simp only [Ty.whnf, hv, Option.getD_some] at this; exact this.symm
      exact (hw.subst σ).trans ((h a (ht a (Ty.TV.of_view_var hv))).trans (hw.subst σ').symm)
    · have hw : TyEq t (.app c xs) := by
        have := TyEq.whnf t; simp only [Ty.whnf, hv, Option.getD_some] at this; exact this.symm
      right
      refine ⟨(Ty.app c xs).subst σ, (Ty.app c xs).subst σ', hw.subst σ, hw.subst σ',
        .inr (.inr ⟨c, xs.map (·.subst σ), xs.map (·.subst σ'), by simp [Ty.view],
          by simp [Ty.view], by simp, fun p hp => ?_⟩)⟩
      rw [List.zip_map] at hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨y, z⟩ := x
      obtain ⟨rfl, hy⟩ := mem_zip_self hx
      exact ⟨y, fun a ha => ht a (Ty.TV.of_view_app hv hy ha), rfl, rfl⟩

/-! ## Computing them -/

/-- Reachable through the graph of `Ty.kids`. -/
inductive Ty.Reach (τ : Ty) : Ty → Prop
  | refl : Ty.Reach τ τ
  | step {x y : Ty} : Ty.Reach τ x → y ∈ x.kids → Ty.Reach τ y

theorem Ty.Reach.trans {τ x y : Ty} (h₁ : τ.Reach x) (h₂ : x.Reach y) : τ.Reach y := by
  induction h₂ with
  | refl => exact h₁
  | step _ hk ih => exact .step ih hk

theorem Ty.reach_view {τ v : Ty} (h : τ.view = some v) : τ.Reach v := by
  cases τ with
  | var a => simp [Ty.view] at h; subst h; exact .refl
  | app c args => simp [Ty.view] at h; subst h; exact .refl
  | mu i sys => exact .step .refl (by simp only [Ty.kids, h, List.mem_singleton])

/-- A kid's tree variables are its parent's. -/
theorem Ty.TV.of_kid {x y : Ty} (hy : y ∈ x.kids) {a : Nat} (h : y.TV a) : x.TV a := by
  cases x with
  | var b => simp [Ty.kids] at hy
  | app c args => exact Ty.TV.of_view_app rfl (by simpa [Ty.kids] using hy) h
  | mu i sys =>
    simp only [Ty.kids] at hy
    split at hy
    · rename_i v hv
      simp only [List.mem_singleton] at hy; subst hy
      obtain ⟨n, hn⟩ := h
      have hview := Ty.view_whnf (Ty.mu i sys)
      rw [Ty.whnf_of_view hv] at hview
      exact ⟨n, by rw [Ty.approx_congr_view hview.symm]; exact hn⟩
    · cases hy

theorem Ty.Reach.tv {τ x : Ty} (h : τ.Reach x) {a : Nat} (hx : x.TV a) : τ.TV a := by
  induction h with
  | refl => exact hx
  | step _ hk ih => exact ih (Ty.TV.of_kid hk hx)

theorem Ty.reach_of_hasVar {a : Nat} : ∀ (n : Nat) (τ : Ty), (τ.approx n).HasVar a →
    τ.Reach (.var a)
  | 0, _, h => absurd h Ty.approx_zero_hasVar
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h
    cases hv : τ.view with
    | none => rw [hv] at h; cases h
    | some t =>
      rw [hv] at h
      have hr := Ty.reach_view hv
      rcases Ty.view_shape hv with ⟨b, rfl⟩ | ⟨c, args, rfl⟩
      · cases h; exact hr
      · dsimp only at h
        cases h with
        | node hm ht =>
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          exact hr.trans ((Ty.Reach.step .refl (by simpa [Ty.kids] using hx)).trans
            (Ty.reach_of_hasVar n x ht))

theorem Ty.tv_iff_reach {τ : Ty} {a : Nat} : τ.TV a ↔ τ.Reach (.var a) :=
  ⟨fun ⟨n, h⟩ => Ty.reach_of_hasVar n τ h, fun h => h.tv (Ty.tv_var_self a)⟩

/-- Add the nodes the kids of `S` reach, one at a time. -/
def reachLoop : Nat → List Ty → List Ty
  | 0, S => S
  | k + 1, S =>
    match (S.flatMap Ty.kids).find? (fun y => decide (y ∉ S)) with
    | none => S
    | some y => reachLoop k (y :: S)

theorem reachLoop_sub : ∀ (k : Nat) (S : List Ty), ∀ x ∈ S, x ∈ reachLoop k S
  | 0, _, _, hx => hx
  | k + 1, S, x, hx => by
    simp only [reachLoop]
    split
    · exact hx
    · exact reachLoop_sub k _ x (List.mem_cons_of_mem _ hx)

theorem reachLoop_reach {τ : Ty} : ∀ (k : Nat) (S : List Ty), (∀ x ∈ S, τ.Reach x) →
    ∀ x ∈ reachLoop k S, τ.Reach x
  | 0, _, h, x, hx => h x hx
  | k + 1, S, h, x, hx => by
    simp only [reachLoop] at hx
    split at hx
    · exact h x hx
    · rename_i y hy
      refine reachLoop_reach k _ (fun z hz => ?_) x hx
      rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨w, hw, hzw⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some hy)
        exact .step (h w hw) hzw
      · exact h z hz

theorem reachLoop_closed {U : List Ty} (hU : KidsClosed U) : ∀ (k : Nat) (S : List Ty),
    S.Nodup → (∀ x ∈ S, x ∈ U) → U.length < S.length + k →
    ∀ x ∈ reachLoop k S, ∀ y ∈ x.kids, y ∈ reachLoop k S
  | 0, S, hnd, hsub, hlen, _, _, _, _ => by
    have := hnd.length_le_of_subset hsub; omega
  | k + 1, S, hnd, hsub, hlen, x, hx, y, hy => by
    simp only [reachLoop] at hx ⊢
    split at hx
    · rename_i hnone
      have := List.find?_eq_none.mp hnone y (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
      simpa using this
    · rename_i z hz
      have hzS : z ∉ S := by simpa using List.find?_some hz
      obtain ⟨w, hw, hzw⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some hz)
      refine reachLoop_closed hU k _ (List.nodup_cons.mpr ⟨hzS, hnd⟩) (fun v hv => ?_)
        (by simp; omega) x hx y hy
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hU w (hsub w hw) _ hzw
      · exact hsub v hv

/-- The nodes a type reaches. -/
def Ty.reachable (τ : Ty) : List Ty := reachLoop (τ.subs.length + 1) [τ]

theorem Ty.mem_reachable {τ x : Ty} : x ∈ τ.reachable ↔ τ.Reach x := by
  refine ⟨fun h => reachLoop_reach _ _ (fun y hy => by simp at hy; subst hy; exact .refl) x h,
    fun h => ?_⟩
  induction h with
  | refl => exact reachLoop_sub _ _ τ (by simp)
  | step _ hk ih =>
    exact reachLoop_closed (U := τ.subs) (Ty.subs_closed τ) _ _ (by simp)
      (fun y hy => by simp at hy; subst hy; exact Ty.mem_subs_self _) (by simp; omega) _ ih _ hk

/-- A type variable's name. -/
def Ty.varOf : Ty → Option Nat
  | .var a => some a
  | _ => none

/-- The tree variables of a type, computed. -/
def Ty.tv (τ : Ty) : List Nat := τ.reachable.filterMap Ty.varOf

theorem Ty.mem_tv {τ : Ty} {a : Nat} : a ∈ τ.tv ↔ τ.TV a := by
  rw [Ty.tv_iff_reach, ← Ty.mem_reachable, Ty.tv, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, he⟩
    cases x <;> simp [Ty.varOf] at he
    subst he; exact hx
  · intro h; exact ⟨_, h, rfl⟩

theorem Ty.tv_sub_ftv {τ : Ty} {a : Nat} (h : a ∈ τ.tv) : a ∈ τ.ftv := (Ty.mem_tv.mp h).ftv

theorem TyEq.mem_tv {s t : Ty} (h : TyEq s t) {a : Nat} : a ∈ s.tv ↔ a ∈ t.tv := by
  rw [Ty.mem_tv, Ty.mem_tv]; exact h.tv

/-! ## Free variables through instantiation, substitution, generalisation -/

theorem RTy.toPTy_ftv (r : RTy) : r.toPTy.ftv = r.ftv := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RTy.toPTy_app, PTy.ftv_app, RTy.ftv_app, List.flatMap_map]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [RTy.toPTy_mu, PTy.ftv_mu, RTy.ftv_mu, List.flatMap_map]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih

theorem Ty.toPTy_ftv (τ : Ty) : τ.toPTy.ftv = τ.ftv := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toPTy_app, PTy.ftv_app, Ty.ftv_app, List.flatMap_map]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih
  | mu i sys =>
    simp only [Ty.toPTy_mu, PTy.ftv_mu, Ty.ftv_mu, List.flatMap_map]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left (fun r _ => RTy.toPTy_ftv r)

theorem PTy.ftv_instR {τs : List Ty} {p : PTy} {a : Nat} (h : a ∈ (p.instR τs).ftv) :
    a ∈ p.ftv ∨ ∃ τ ∈ τs, a ∈ τ.ftv := by
  induction p using PTy.ind with
  | free b => simp [PTy.instR, RTy.ftv] at h; simp [PTy.ftv, h]
  | bound i =>
    simp only [PTy.instR, List.getD_eq_getElem?_getD, Ty.toRTy_ftv] at h
    cases hi : τs[i]? with
    | none => simp [hi] at h
    | some τ => simp only [hi, Option.getD_some] at h; exact .inr ⟨τ, List.mem_of_getElem? hi, h⟩
  | self j => simp [PTy.instR, RTy.ftv] at h
  | app c args ih =>
    simp only [PTy.instR_app, RTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    simp only [PTy.ftv_app, List.mem_flatMap]
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    rcases ih q hq h with h | h
    · exact .inl ⟨q, hq, h⟩
    · exact .inr h
  | mu i sys ih =>
    simp only [PTy.instR_mu, RTy.ftv_mu, List.mem_flatMap, List.mem_map] at h
    simp only [PTy.ftv_mu, List.mem_flatMap]
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    rcases ih q hq h with h | h
    · exact .inl ⟨q, hq, h⟩
    · exact .inr h

theorem PTy.ftv_inst {τs : List Ty} {p : PTy} {a : Nat} (h : a ∈ (p.inst τs).ftv) :
    a ∈ p.ftv ∨ ∃ τ ∈ τs, a ∈ τ.ftv := by
  induction p using PTy.ind with
  | free b => simp [PTy.inst] at h; simp [PTy.ftv, h]
  | bound i =>
    simp only [PTy.inst, List.getD_eq_getElem?_getD] at h
    cases hi : τs[i]? with
    | none => simp [hi] at h
    | some τ => simp only [hi, Option.getD_some] at h; exact .inr ⟨τ, List.mem_of_getElem? hi, h⟩
  | self j => simp [PTy.inst] at h
  | app c args ih =>
    simp only [PTy.inst_app, Ty.ftv_app, List.mem_flatMap, List.mem_map] at h
    simp only [PTy.ftv_app, List.mem_flatMap]
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    rcases ih q hq h with h | h
    · exact .inl ⟨q, hq, h⟩
    · exact .inr h
  | mu i sys _ =>
    simp only [PTy.inst_mu, Ty.ftv_mu, List.mem_flatMap, List.mem_map] at h
    simp only [PTy.ftv_mu, List.mem_flatMap]
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    rcases PTy.ftv_instR h with h | h
    · exact .inl ⟨q, hq, h⟩
    · exact .inr h

theorem PTy.ftv_subst {σ : Subst} {p : PTy} {a : Nat} (h : a ∈ (p.subst σ).ftv) :
    ∃ b ∈ p.ftv, a ∈ ((Ty.var b).subst σ).ftv := by
  induction p using PTy.ind with
  | free b =>
    simp only [PTy.subst, Ty.toPTy_ftv] at h
    exact ⟨b, by simp [PTy.ftv], by simpa [Ty.subst] using h⟩
  | bound i => simp [PTy.subst, PTy.ftv] at h
  | self j => simp [PTy.subst, PTy.ftv] at h
  | app c args ih =>
    simp only [PTy.subst_app, PTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    obtain ⟨b, hb, h⟩ := ih q hq h
    exact ⟨b, by simp only [PTy.ftv_app, List.mem_flatMap]; exact ⟨q, hq, hb⟩, h⟩
  | mu i sys ih =>
    simp only [PTy.subst_mu, PTy.ftv_mu, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    obtain ⟨b, hb, h⟩ := ih q hq h
    exact ⟨b, by simp only [PTy.ftv_mu, List.mem_flatMap]; exact ⟨q, hq, hb⟩, h⟩

theorem RTy.gen_ftv {ᾱ : List Nat} {r : RTy} {a : Nat} (h : a ∈ (r.gen ᾱ).ftv) : a ∈ r.ftv := by
  induction r using RTy.ind with
  | free b =>
    simp only [RTy.gen] at h
    split at h <;> simp_all [PTy.ftv, RTy.ftv]
  | self j => simp [RTy.gen, PTy.ftv] at h
  | app c args ih =>
    simp only [RTy.gen_app, PTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    simp only [RTy.ftv_app, List.mem_flatMap]
    exact ⟨q, hq, ih q hq h⟩
  | mu i sys ih =>
    simp only [RTy.gen_mu, PTy.ftv_mu, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    simp only [RTy.ftv_mu, List.mem_flatMap]
    exact ⟨q, hq, ih q hq h⟩

theorem Ty.gen_ftv {ᾱ : List Nat} {τ : Ty} {a : Nat} (h : a ∈ (τ.gen ᾱ).ftv) : a ∈ τ.ftv := by
  induction τ using Ty.ind with
  | var b =>
    simp only [Ty.gen] at h
    split at h <;> simp_all [PTy.ftv]
  | app c args ih =>
    simp only [Ty.gen_app, PTy.ftv_app, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    simp only [Ty.ftv_app, List.mem_flatMap]
    exact ⟨q, hq, ih q hq h⟩
  | mu i sys =>
    simp only [Ty.gen_mu, PTy.ftv_mu, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := h
    simp only [Ty.ftv_mu, List.mem_flatMap]
    exact ⟨q, hq, RTy.gen_ftv h⟩


/-! ## Fresh blocks of variables -/

theorem Subst.block_find_none {m : Nat} {τs : List Ty} {a : Nat} (h : a < m) :
    (Subst.block m τs).find a = none :=
  Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)

theorem Subst.block_find_ge {m : Nat} {τs : List Ty} {a : Nat} (h : m + τs.length ≤ a) :
    (Subst.block m τs).find a = none :=
  Subst.find_none (fun p hp e => by
    have := (List.of_mem_zip hp).1
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp this; omega)

theorem PTy.instR_open_block_append {n : Nat} {τs : List Ty} {ψ : Subst} (p : PTy)
    (hp : ∀ a ∈ p.ftv, a < n) :
    (p.instR (varBlock n τs.length)).subst (Subst.block n τs ++ ψ) = (p.subst ψ).instR τs := by
  induction p using PTy.ind with
  | free a =>
    have ha := hp a (by simp [PTy.ftv])
    simp [PTy.instR, PTy.subst, RTy.subst, Subst.find_append, Subst.block_find_none ha]
  | bound i =>
    simp only [varBlock, PTy.instR, PTy.subst, Ty.toRTy_subst, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.find_append, Subst.block_find]
    · simp [hi]
  | self j => rfl
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at hp
    simp only [PTy.instR_app, PTy.subst_app, RTy.subst_app, List.map_map, RTy.app.injEq,
      true_and]
    exact List.map_congr_left (fun q hq => ih q hq (fun a ha => hp a ⟨q, hq, ha⟩))
  | mu i sys ih =>
    simp only [PTy.ftv_mu, List.mem_flatMap] at hp
    simp only [PTy.instR_mu, PTy.subst_mu, RTy.subst_mu, List.map_map, RTy.mu.injEq, true_and]
    exact List.map_congr_left (fun q hq => ih q hq (fun a ha => hp a ⟨q, hq, ha⟩))

/-- Opening a scheme at fresh variables, then sending them to `τs` and the
rest by `ψ`, is instantiating the `ψ`-substituted scheme at `τs`. -/
theorem PTy.open_block_append {n : Nat} {τs : List Ty} {ψ : Subst} (p : PTy)
    (hp : ∀ a ∈ p.ftv, a < n) :
    (p.inst (varBlock n τs.length)).subst (Subst.block n τs ++ ψ) = (p.subst ψ).inst τs := by
  induction p using PTy.ind with
  | free a =>
    have ha := hp a (by simp [PTy.ftv])
    simp [PTy.inst, PTy.subst, Ty.subst, Subst.find_append, Subst.block_find_none ha]
  | bound i =>
    simp only [varBlock, PTy.inst, PTy.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < τs.length
    · simp [hi, Ty.subst, Subst.find_append, Subst.block_find]
    · simp [hi]
  | self j => rfl
  | app c args ih =>
    simp only [PTy.ftv_app, List.mem_flatMap] at hp
    simp only [PTy.inst_app, PTy.subst_app, Ty.subst_app, List.map_map, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun q hq => ih q hq (fun a ha => hp a ⟨q, hq, ha⟩))
  | mu i sys _ =>
    simp only [PTy.ftv_mu, List.mem_flatMap] at hp
    simp only [PTy.inst_mu, PTy.subst_mu, Ty.subst_mu, List.map_map, Ty.mu.injEq, true_and]
    exact List.map_congr_left (fun q hq =>
      PTy.instR_open_block_append q (fun a ha => hp a ⟨q, hq, ha⟩))

theorem Scheme.open_block_append {n : Nat} {τs : List Ty} {ψ : Subst} {s : Scheme}
    (hs : ∀ a ∈ s.ftv, a < n) (hlen : τs.length = s.arity) :
    (s.open n).subst (Subst.block n τs ++ ψ) = (s.subst ψ).inst τs := by
  simp only [Scheme.open, Scheme.inst, Scheme.subst, ← hlen]
  exact PTy.open_block_append _ (fun a ha => hs a (List.mem_append_left _ ha))

theorem Scheme.openPreds_block_append {n : Nat} {τs : List Ty} {ψ : Subst} {s : Scheme}
    (hs : ∀ a ∈ s.ftv, a < n) (hlen : τs.length = s.arity) :
    (s.openPreds n).map (·.subst (Subst.block n τs ++ ψ)) = (s.subst ψ).instPreds τs := by
  simp only [Scheme.openPreds, Scheme.instPreds, Scheme.subst, List.map_map, ← hlen]
  refine List.map_congr_left (fun q hq => ?_)
  obtain ⟨c, args⟩ := q
  simp only [Function.comp, PPred.inst, Pred.subst, PPred.subst, List.map_map, Pred.mk.injEq,
    true_and]
  exact List.map_congr_left (fun r hr => PTy.open_block_append r (fun a ha =>
    hs a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hq,
      List.mem_flatMap.mpr ⟨r, hr, ha⟩⟩))))

/-! ## Constraints and schemes -/

/-- The tree variables of a constraint. -/
def Pred.tv (p : Pred) : List Nat := p.args.flatMap Ty.tv

/-- Constants for a scheme's quantified variables: read at them, a scheme
shows the tree variables of its own. -/
def Scheme.consts (s : Scheme) : List Ty := List.replicate s.arity .undefined

/-- The tree variables of a scheme, not counting its quantified ones. -/
def Scheme.tv (s : Scheme) : List Nat :=
  (s.inst s.consts).tv ++ (s.instPreds s.consts).flatMap Pred.tv

/-- The tree variables of a context. -/
def ctxTv (Γ : Ctx) : List Nat := Γ.flatMap Scheme.tv

theorem Pred.tv_sub_ftv {p : Pred} {a : Nat} (h : a ∈ p.tv) : a ∈ p.ftv := by
  simp only [Pred.tv, Pred.ftv, List.mem_flatMap] at h ⊢
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, ht, Ty.tv_sub_ftv h⟩

theorem Scheme.consts_subst (σ : Subst) (s : Scheme) :
    s.consts.map (·.subst σ) = s.consts := by
  simp [Scheme.consts, List.map_replicate]

theorem Scheme.consts_ftv {s : Scheme} {a : Nat} : ¬ ∃ τ ∈ s.consts, a ∈ τ.ftv := by
  simp [Scheme.consts]

theorem Scheme.tv_sub_ftv {s : Scheme} {a : Nat} (h : a ∈ s.tv) : a ∈ s.ftv := by
  simp only [Scheme.tv, List.mem_append, List.mem_flatMap] at h
  simp only [Scheme.ftv, List.mem_append, List.mem_flatMap]
  rcases h with h | ⟨p, hp, h⟩
  · rcases PTy.ftv_inst (Ty.tv_sub_ftv h) with h | h
    · exact .inl h
    · exact absurd h Scheme.consts_ftv
  · simp only [Scheme.instPreds, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := Pred.tv_sub_ftv h
    simp only [Pred.ftv, PPred.inst, List.flatMap_map, List.mem_flatMap] at this
    obtain ⟨r, hr, h⟩ := this
    rcases PTy.ftv_inst h with h | h
    · exact .inr ⟨q, hq, List.mem_flatMap.mpr ⟨r, hr, h⟩⟩
    · exact absurd h Scheme.consts_ftv

theorem ctxTv_sub_ftv {Γ : Ctx} {a : Nat} (h : a ∈ ctxTv Γ) : a ∈ ctxFtv Γ := by
  simp only [ctxTv, ctxFtv, List.mem_flatMap] at h ⊢
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, Scheme.tv_sub_ftv h⟩

/-- A constraint's tree variables through substitution. -/
theorem Pred.tv_subst {σ : Subst} {p : Pred} {b : Nat} (h : b ∈ (p.subst σ).tv) :
    ∃ a, a ∈ p.tv ∧ ((Ty.var a).subst σ).TV b := by
  simp only [Pred.tv, Pred.subst, List.flatMap_map, List.mem_flatMap] at h
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨a, ha, hb⟩ := Ty.TV.subst_inv (Ty.mem_tv.mp h)
  exact ⟨a, List.mem_flatMap.mpr ⟨t, ht, Ty.mem_tv.mpr ha⟩, hb⟩

theorem Pred.tv_subst_of {σ : Subst} {p : Pred} {a b : Nat} (ha : a ∈ p.tv)
    (hb : ((Ty.var a).subst σ).TV b) : b ∈ (p.subst σ).tv := by
  simp only [Pred.tv, Pred.subst, List.flatMap_map, List.mem_flatMap] at ha ⊢
  obtain ⟨t, ht, ha⟩ := ha
  exact ⟨t, ht, Ty.mem_tv.mpr (Ty.TV.subst_of (Ty.mem_tv.mp ha) hb)⟩

/-- A scheme's tree variables through substitution come from its free
variables. -/
theorem Scheme.tv_subst {σ : Subst} {s : Scheme} {b : Nat} (h : b ∈ (s.subst σ).tv) :
    ∃ a ∈ s.ftv, ((Ty.var a).subst σ).TV b := by
  have hc : (s.subst σ).consts = s.consts := by simp [Scheme.consts]
  simp only [Scheme.tv, hc, List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨p, hp, h⟩
  · rw [← Scheme.consts_subst σ s, ← Scheme.inst_subst] at h
    obtain ⟨a, ha, hb⟩ := Ty.TV.subst_inv (Ty.mem_tv.mp h)
    exact ⟨a, Scheme.tv_sub_ftv (by simp [Scheme.tv, Ty.mem_tv.mpr ha]), hb⟩
  · rw [← Scheme.consts_subst σ s, ← Scheme.instPreds_subst] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha, hb⟩ := Pred.tv_subst h
    exact ⟨a, Scheme.tv_sub_ftv (by
      simp only [Scheme.tv, List.mem_append, List.mem_flatMap]; exact .inr ⟨q, hq, ha⟩), hb⟩

theorem ctxTv_subst {σ : Subst} {Γ : Ctx} {b : Nat} (h : b ∈ ctxTv (Ctx.subst σ Γ)) :
    ∃ a ∈ ctxFtv Γ, ((Ty.var a).subst σ).TV b := by
  simp only [ctxTv, Ctx.subst, List.flatMap_map, List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨a, ha, hb⟩ := Scheme.tv_subst h
  exact ⟨a, List.mem_flatMap.mpr ⟨s, hs, ha⟩, hb⟩

/-! ## Equal schemes -/

/-- Constraints equal through substitutions that agree on their tree
variables. -/
theorem Pred.subst_predEq_congr_tv {σ σ' : Subst} {p : Pred}
    (h : ∀ a ∈ p.tv, TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    PredEq (p.subst σ) (p.subst σ') := by
  refine ⟨rfl, by simp [Pred.subst], fun x hx => ?_⟩
  simp only [Pred.subst, List.zip_map] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨t, t'⟩ := y
  obtain ⟨rfl, ht⟩ := mem_zip_self hy
  exact Ty.subst_tyEq_congr_tv (fun a ha =>
    h a (List.mem_flatMap.mpr ⟨t, ht, Ty.mem_tv.mpr ha⟩))

/-- Two schemes with equal instances, constraint by constraint. -/
def SchemeEq (s s' : Scheme) : Prop :=
  s.arity = s'.arity ∧ s.preds.length = s'.preds.length ∧ ∀ τs, τs.length = s.arity →
    TyEq (s.inst τs) (s'.inst τs) ∧ ∀ x ∈ (s.instPreds τs).zip (s'.instPreds τs), PredEq x.1 x.2

theorem SchemeEq.refl (s : Scheme) : SchemeEq s s :=
  ⟨rfl, rfl, fun τs _ => ⟨TyEq.refl _, fun x hx => by
    obtain ⟨y, z⟩ := x
    obtain ⟨rfl, -⟩ := mem_zip_self hx
    exact PredEq.refl _⟩⟩

theorem zip_symm_mem {α β : Type} : ∀ {l₁ : List α} {l₂ : List β} {a : α} {b : β},
    (b, a) ∈ l₂.zip l₁ → (a, b) ∈ l₁.zip l₂
  | _ :: _, _ :: _, _, _, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (zip_symm_mem h)
  | [], _, _, _, h | _ :: _, [], _, _, h => by simp at h

theorem SchemeEq.symm {s s' : Scheme} (h : SchemeEq s s') : SchemeEq s' s :=
  ⟨h.1.symm, h.2.1.symm, fun τs hl => by
    obtain ⟨he, hp⟩ := h.2.2 τs (hl.trans h.1.symm)
    refine ⟨he.symm, fun x hx => ?_⟩
    obtain ⟨y, z⟩ := x
    exact (hp (z, y) (zip_symm_mem hx)).symm⟩

theorem zip_trans_mem {α β γ : Type} : ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ},
    l₂.length = l₃.length → ∀ {a : α} {c : γ}, (a, c) ∈ l₁.zip l₃ →
      ∃ b, (a, b) ∈ l₁.zip l₂ ∧ (b, c) ∈ l₂.zip l₃
  | _ :: _, b :: _, _ :: _, hl, _, _, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨b, by simp, by simp⟩
    · obtain ⟨b', h₁, h₂⟩ := zip_trans_mem (by simpa using hl) h
      exact ⟨b', List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩
  | [], _, _, _, _, _, h | _ :: _, _, [], _, _, _, h => by simp at h
  | _ :: _, [], _ :: _, hl, _, _, _ => by simp at hl

theorem SchemeEq.trans {s s' s'' : Scheme} (h₁ : SchemeEq s s') (h₂ : SchemeEq s' s'') :
    SchemeEq s s'' :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun τs hl => by
    obtain ⟨he₁, hp₁⟩ := h₁.2.2 τs hl
    obtain ⟨he₂, hp₂⟩ := h₂.2.2 τs (hl.trans h₁.1)
    refine ⟨he₁.trans he₂, fun x hx => ?_⟩
    obtain ⟨a, c⟩ := x
    obtain ⟨b, hab, hbc⟩ := zip_trans_mem (l₂ := s'.instPreds τs) (by simp [Scheme.instPreds]; exact h₂.2.1) hx
    exact PredEq.trans (hp₁ (a, b) hab) (hp₂ (b, c) hbc)⟩

theorem zip_map_map_mem {α β : Type} {f g : α → β} : ∀ {l : List α} {x : β × β},
    x ∈ (l.map f).zip (l.map g) → ∃ a ∈ l, x = (f a, g a)
  | a :: l, x, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := zip_map_map_mem h
      exact ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
  | [], _, h => by simp at h

/-- Substitutions that agree on a scheme's tree variables give equal
schemes. -/
theorem Scheme.subst_congr_tv {σ σ' : Subst} {s : Scheme}
    (h : ∀ a ∈ s.tv, TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    SchemeEq (s.subst σ) (s.subst σ') := by
  refine ⟨by simp, by simp [Scheme.subst], fun τs hl => ?_⟩
  simp only [Scheme.subst_arity] at hl
  have hM : ∀ a ∈ s.ftv, a < maxPlusOne s.ftv := lt_maxPlusOne
  generalize maxPlusOne s.ftv = M at hM
  have hcl : s.consts.length = s.arity := by simp [Scheme.consts]
  -- A tree variable of the scheme opened at `M` is in the block or the
  -- scheme's own.
  have key : ∀ a t, (t ∈ [s.open M] ∨ ∃ q ∈ s.openPreds M, t ∈ q.args) → t.TV a →
      TyEq ((Ty.var a).subst (Subst.block M τs ++ σ)) ((Ty.var a).subst (Subst.block M τs ++ σ')) := by
    intro a t ht hta
    cases hB : (Subst.block M τs).find a with
    | some u => simp [Ty.subst, Subst.find_append, hB]; exact TyEq.refl _
    | none =>
      have hsub : ∀ τ' : Ty, (Ty.var a).subst (Subst.block M τs ++ τ'.ftv.map (fun _ => (0, τ'))) = (Ty.var a).subst (Subst.block M τs ++ τ'.ftv.map (fun _ => (0, τ'))) := fun _ => rfl
      clear hsub
      simp only [Ty.subst, Subst.find_append, hB]
      have hfa : a ∈ s.ftv := by
        have haf : a ∈ t.ftv := hta.ftv
        have hin : ∀ p : PTy, a ∈ (p.inst (varBlock M s.arity)).ftv → a ∈ p.ftv := fun p hp => by
          rcases PTy.ftv_inst hp with hp | ⟨τ, hτ, hp⟩
          · exact hp
          · simp only [varBlock, List.mem_map, List.mem_range'] at hτ
            obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hτ
            simp only [Ty.ftv_var, List.mem_singleton, Nat.one_mul] at hp hB; subst hp
            have := Subst.block_find M τs i
            rw [hB, eq_comm, List.getElem?_eq_none_iff] at this
            omega
        rcases ht with ht | ⟨q, hq, ht⟩
        · simp only [List.mem_singleton] at ht; subst ht
          exact List.mem_append_left _ (hin _ haf)
        · simp only [Scheme.openPreds, Scheme.instPreds, List.mem_map] at hq
          obtain ⟨q₀, hq₀, rfl⟩ := hq
          simp only [PPred.inst, List.mem_map] at ht
          obtain ⟨r, hr, rfl⟩ := ht
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨q₀, hq₀,
            List.mem_flatMap.mpr ⟨r, hr, hin r haf⟩⟩)
      have hblock : (Ty.var a).subst (Subst.block M s.consts) = .var a := by
        simp [Ty.subst, Subst.block_find_none (hM a hfa)]
      have hta' : (t.subst (Subst.block M s.consts)).TV a :=
        Ty.TV.subst_of hta (by rw [hblock]; exact Ty.tv_var_self a)
      refine h a ?_
      rcases ht with ht | ⟨q, hq, ht⟩
      · simp only [List.mem_singleton] at ht; subst ht
        rw [Scheme.open_block s hM hcl] at hta'
        simp [Scheme.tv, Ty.mem_tv.mpr hta']
      · simp only [Scheme.tv, List.mem_append, List.mem_flatMap]
        refine .inr ⟨q.subst (Subst.block M s.consts), ?_, ?_⟩
        · rw [← Scheme.openPreds_block s hM hcl]; exact List.mem_map_of_mem hq
        · simp only [Pred.tv, Pred.subst, List.flatMap_map, List.mem_flatMap]
          exact ⟨t, ht, Ty.mem_tv.mpr hta'⟩
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← Scheme.open_block_append hM hl, ← Scheme.open_block_append hM hl]
    exact Ty.subst_tyEq_congr_tv (fun a ha => key a _ (.inl (List.mem_singleton_self _)) ha)
  · rw [← Scheme.openPreds_block_append hM hl, ← Scheme.openPreds_block_append hM hl] at hx
    obtain ⟨q, hq, rfl⟩ := zip_map_map_mem hx
    refine ⟨rfl, by simp [Pred.subst], fun y hy => ?_⟩
    simp only [Pred.subst, List.zip_map] at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    obtain ⟨t, t'⟩ := z
    obtain ⟨rfl, ht⟩ := mem_zip_self hz
    exact Ty.subst_tyEq_congr_tv (fun a ha => key a t (.inr ⟨q, hq, ht⟩) ha)

/-- Substitutions equal on a scheme's free variables give equal schemes. -/
theorem Scheme.subst_congr_ftv {σ σ' : Subst} {s : Scheme}
    (h : ∀ a ∈ s.ftv, TyEq ((Ty.var a).subst σ) ((Ty.var a).subst σ')) :
    SchemeEq (s.subst σ) (s.subst σ') :=
  Scheme.subst_congr_tv (fun a ha => h a (Scheme.tv_sub_ftv ha))

end Inty
