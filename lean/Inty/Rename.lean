import Inty.Rigid
import Inty.Infer

/-!
# Renaming rigid type variables

A polymorphic annotation's initialiser is typed at the rigid type variables
of any name outside a finite set (`HasTypeS.letPoly`). Inference types it
at one name; swapping that name with another (`RSubst.swap`) gives the
rest. A swap renames rigid type variables to rigid type variables
(`RSubst.Renaming`), which the narrow system's instances survive
(`Sys.narrow_rsubstable`); it undoes itself (`RSubst.Invol`) and commutes
with substitution (`Ty.subst_rsub`).
-/

namespace Inty

/-- `ρ` renames rigid type variables: each image is one. -/
def RSubst.Renaming (ρ : RSubst) : Prop :=
  ∀ s i t, ρ s i = some t → ∃ s' i', t = .app (.rigid s' i') []

/-- `ρ` undoes itself. -/
def RSubst.Invol (ρ : RSubst) : Prop := ∀ s i t, ρ s i = some t → t.rsub ρ = .app (.rigid s i) []

/-- Swapping the names `k` and `k'` of rigid type variables. -/
def RSubst.swap (k k' : Nat) : RSubst := fun s i =>
  if s = k then some (.app (.rigid k' i) []) else if s = k' then some (.app (.rigid k i) []) else none

theorem RSubst.swap_renaming (k k' : Nat) : (RSubst.swap k k').Renaming := by
  intro s i t h
  unfold RSubst.swap at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · split at h
    · cases h; exact ⟨_, _, rfl⟩
    · cases h

theorem RSubst.swap_invol (k k' : Nat) : (RSubst.swap k k').Invol := by
  intro s i t h
  unfold RSubst.swap at h
  by_cases h1 : s = k
  · subst h1; simp only [↓reduceIte, Option.some.injEq] at h; subst h
    by_cases h2 : k' = s
    · subst h2; simp [Con.rimgA, Con.rimg, RSubst.swap]
    · simp [Con.rimgA, Con.rimg, RSubst.swap, h2]
  · by_cases h2 : s = k'
    · subst h2; simp only [h1, ↓reduceIte, Option.some.injEq] at h; subst h
      simp [Con.rimgA, Con.rimg, RSubst.swap]
    · simp [h1, h2] at h

theorem rigids_rsub_swap (k k' n : Nat) :
    (rigids k n).map (·.rsub (RSubst.swap k k')) = rigids k' n := by
  simp [rigids, Con.rimgA, Con.rimg, RSubst.swap]

theorem RSubst.swap_dom {k k' s i : Nat} {t : Ty} (h : RSubst.swap k k' s i = some t) :
    s ∈ [k, k'] := by
  unfold RSubst.swap at h
  split at h
  · simp_all
  · split at h
    · simp_all
    · cases h

/-- The names a swap leaves. -/
theorem RSubst.swap_off {k k' : Nat} {ks : List Nat} (hk : k ∉ ks) (hk' : k' ∉ ks) :
    (RSubst.swap k k').Off ks := fun s hs i => by
  have h1 : s ≠ k := fun e => hk (e ▸ hs)
  have h2 : s ≠ k' := fun e => hk' (e ▸ hs)
  simp [RSubst.swap, h1, h2]

theorem Ty.toPTy_rsub (ρ : RSubst) (τ : Ty) : τ.toPTy.rsub ρ = (τ.rsub ρ).toPTy :=
  congrArg Scheme.body (Scheme.mono_rsub ρ τ)

/-! ## A renaming's images -/

private theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem Con.rimg_ren {ρ : RSubst} (hρ : ρ.Renaming) {c : Con} {t : Ty} (h : c.rimg ρ = some t) :
    ∃ s i s' i', c = .rigid s i ∧ ρ s i = some t ∧ t = .app (.rigid s' i') [] := by
  cases c <;> simp only [Con.rimg, reduceCtorEq] at h
  obtain ⟨s', i', rfl⟩ := hρ _ _ _ h
  exact ⟨_, _, s', i', rfl, h, rfl⟩

/-- A renamed constructor application: a rigid type variable renamed, or
the constructor over its arguments renamed. -/
theorem Ty.rsub_app_ren {ρ : RSubst} (hρ : ρ.Renaming) (c : Con) (args : List Ty) :
    (∃ s i s' i', c = .rigid s i ∧ args = [] ∧ (Ty.app c args).rsub ρ = .app (.rigid s' i') []) ∨
      (Ty.app c args).rsub ρ = .app c (args.map (·.rsub ρ)) := by
  cases h : c.rimgA ρ args with
  | some t =>
    obtain ⟨hc, rfl⟩ := Con.rimgA_some h
    obtain ⟨s, i, s', i', rfl, _, rfl⟩ := Con.rimg_ren hρ hc
    exact .inl ⟨s, i, s', i', rfl, rfl, Ty.rsub_app_some h⟩
  | none => exact .inr (Ty.rsub_app_none h)

theorem RTy.ftv_rsub_ren {ρ : RSubst} (hρ : ρ.Renaming) (r : RTy) : (r.rsub ρ).ftv = r.ftv := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    rw [RTy.rsub_app]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := Con.rimg_ren hρ hc
      simp
    | none =>
      simp only [RTy.ftv_app, List.flatMap_map]
      exact flatMap_congr' ih
  | mu i sys ih =>
    simp only [RTy.rsub_mu, RTy.ftv_mu, List.flatMap_map]
    exact flatMap_congr' ih

/-- A renaming keeps a type's type variables. -/
theorem Ty.ftv_rsub_ren {ρ : RSubst} (hρ : ρ.Renaming) (τ : Ty) : (τ.rsub ρ).ftv = τ.ftv := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    rw [Ty.rsub_app]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := Con.rimg_ren hρ hc
      simp
    | none =>
      simp only [Ty.ftv_app, List.flatMap_map]
      exact flatMap_congr' ih
  | mu i sys =>
    simp only [Ty.rsub_mu, Ty.ftv_mu, List.flatMap_map]
    exact flatMap_congr' fun r _ => RTy.ftv_rsub_ren hρ r

/-! ## The narrow system survives renaming -/

theorem Inst.rsub {ρ : RSubst} (hρ : ρ.Renaming) {p : Pred} (h : Inst p) : Inst (p.rsub ρ) := by
  induction h with
  | plusNumber => exact .plusNumber
  | plusString => exact .plusString
  | @hasProp l ls fs k σ hf =>
    have : Ty.field l ls (fs.map (·.rsub ρ)) = some (.slot .pre (k.rsub ρ) (σ.rsub ρ)) := by
      simp [Ty.field_rsub, hf]
    simpa [Pred.rsub] using Inst.hasProp this
  | mergeData => simpa [Pred.rsub] using Inst.mergeData
  | mergeGetter => simpa [Pred.rsub] using Inst.mergeGetter
  | mergeAbs hs => simpa [Pred.rsub] using Inst.mergeAbs (hs.rsub ρ)
  | mergeProto hs => simpa [Pred.rsub] using Inst.mergeProto (hs.rsub ρ)
  | lengthArray => simpa [Pred.rsub] using Inst.lengthArray
  | lengthString => simpa [Pred.rsub] using Inst.lengthString
  | indexArray => simpa [Pred.rsub] using Inst.indexArray
  | indexString => simpa [Pred.rsub] using Inst.indexString
  | writeArray => simpa [Pred.rsub] using Inst.writeArray
  | @notNew c args hn =>
    have hr : c.isRigid = false := by
      cases hc' : c.isRigid
      · rfl
      · exact absurd (.inr hc') hn
    simpa [Pred.rsub, Ty.rsub_app_nr hr] using
      Inst.notNew (c := c) (args := args.map (·.rsub ρ)) hn
  | @injectSelf T hT =>
    simpa [Pred.rsub, Cls.rsub] using
      Inst.injectSelf (T := T.rsub ρ) (by rw [Ty.ftv_rsub_ren hρ]; exact hT)
  | @injectNothing T z σ he hT =>
    simpa [Pred.rsub, Cls.rsub] using
      Inst.injectNothing (z := z) (σ := σ.rsub ρ) (by simpa using he.rsub ρ)
        (by rw [Ty.ftv_rsub_ren hρ]; exact hT)
  | @injectSome T z c args he hT ha hc hz =>
    have hT' : (T.rsub ρ).ftv = [] := by rw [Ty.ftv_rsub_ren hρ]; exact hT
    rcases Ty.rsub_app_ren hρ c args with ⟨s, i, s', i', rfl, rfl, heq⟩ | heq
    · have he' := he.rsub ρ
      simp only [Ty.rsub_maybe, heq] at he'
      simpa [Pred.rsub, Cls.rsub, heq] using
        Inst.injectSome (args := []) he' hT' (by simp) (by simp) (by cases z <;> simp [Nothing.con])
    · have he' := he.rsub ρ
      simp only [Ty.rsub_maybe, heq] at he'
      have ha' : (Ty.app c (args.map (·.rsub ρ))).ftv = [] := by
        rw [← heq, Ty.ftv_rsub_ren hρ]; exact ha
      simpa [Pred.rsub, Cls.rsub, heq] using
        Inst.injectSome he' hT' ha' hc (by simpa using hz)
  | stripSome => simpa [Pred.rsub] using Inst.stripSome
  | injectArm hT hw hn htag hi hR he ha =>
    have hr := Con.isRigid_of_typeTag htag
    have hT' := (Ty.ftv_rsub_ren hρ _).trans hT
    have ha' := (Ty.ftv_rsub_ren hρ _).trans ha
    have he' := he.rsub ρ
    rw [Ty.rsub_app_nr hr] at he' ha'
    simpa [Pred.rsub, Cls.rsub, Ty.rsub_app_nr hr] using
      Inst.injectArm hT' (Ty.whnf_rsub_nr hw rfl) hn htag hi (by simp [hR]) he' ha'
  | injectLit _ hx ih =>
    simpa [Pred.rsub, Cls.rsub, Ty.rsub_app, Con.rimgA, Con.rimg] using
      Inst.injectLit (by simpa [Pred.rsub, Cls.rsub] using ih)
        (by simpa [Ty.rsub_app, Con.rimgA, Con.rimg] using hx.rsub ρ)
  | @caseHit ts i t Rs R d hn hi hR =>
    simpa [Pred.rsub, Cls.rsub, variantRest_rsub, ← eraseIdx_map, Ty.rsub_app, Con.rimgA,
      Con.rimg] using Inst.caseHit (d := d) (ts := ts) hn hi (by simp [hR])
  | @stripSelf c args h₁ h₂ h₃ =>
    rcases Ty.rsub_app_ren hρ c args with ⟨s, i, s', i', rfl, rfl, heq⟩ | heq
    · simpa [Pred.rsub, heq] using
        Inst.stripSelf (c := .rigid s' i') (args := []) (by simp) (by simp) (by simp)
    · simpa [Pred.rsub, heq] using Inst.stripSelf (args := args.map (·.rsub ρ)) h₁ h₂ h₃

theorem InstEq.rsub {ρ : RSubst} (hρ : ρ.Renaming) {p : Pred} (h : InstEq p) : InstEq (p.rsub ρ) :=
  let ⟨q, hpq, hq⟩ := h
  ⟨q.rsub ρ, hpq.rsub ρ, Inst.rsub hρ hq⟩

/-- The narrow system survives renaming rigid type variables. -/
theorem Sys.narrow_rsubstable {ρ : RSubst} (hρ : ρ.Renaming) : Sys.narrow.RSubstable ρ where
  inst := fun h => InstEq.rsub hρ h
  closed := fun {T} hT => by
    show (T.rsub ρ).ftv = []
    rw [Ty.ftv_rsub_ren hρ]; exact hT
  injPred _ _ := by simp [Sys.narrow, Pred.rsub, Cls.rsub]

/-! ## A swap undoes itself -/

theorem RTy.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (r : RTy) : (r.rsub ρ).rsub ρ = r := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    rw [RTy.rsub_app ρ c args]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      dsimp only
      cases c <;> simp only [Con.rimg, reduceCtorEq] at hc
      rw [Ty.toRTy_rsub, hρ _ _ t hc]; simp
    | none =>
      dsimp only
      rw [RTy.rsub_app_none (by rwa [Con.rimgA_map]), List.map_map]
      congr 1
      exact (List.map_congr_left fun p hp => ih p hp).trans (List.map_id _)
  | mu i sys ih =>
    simp only [RTy.rsub_mu, List.map_map]
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp).trans (List.map_id _)

theorem Ty.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (τ : Ty) : (τ.rsub ρ).rsub ρ = τ := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    rw [Ty.rsub_app ρ c args]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      dsimp only
      cases c <;> simp only [Con.rimg, reduceCtorEq] at hc
      exact hρ _ _ t hc
    | none =>
      dsimp only
      rw [Ty.rsub_app_none (by rwa [Con.rimgA_map]), List.map_map]
      congr 1
      exact (List.map_congr_left fun p hp => ih p hp).trans (List.map_id _)
  | mu i sys =>
    simp only [Ty.rsub_mu, List.map_map]
    congr 1
    exact (List.map_congr_left fun p _ => RTy.rsub_invol hρ p).trans (List.map_id _)

theorem PTy.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (p : PTy) : (p.rsub ρ).rsub ρ = p := by
  induction p using PTy.ind with
  | free a => rfl
  | bound i => rfl
  | self j => rfl
  | app c args ih =>
    rw [PTy.rsub_app ρ c args]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      dsimp only
      cases c <;> simp only [Con.rimg, reduceCtorEq] at hc
      rw [Ty.toPTy_rsub, hρ _ _ t hc]; simp
    | none =>
      dsimp only
      rw [PTy.rsub_app, Con.rimgA_map, h]
      dsimp only
      rw [List.map_map]
      congr 1
      exact (List.map_congr_left fun p hp => ih p hp).trans (List.map_id _)
  | mu i sys ih =>
    simp only [PTy.rsub_mu, List.map_map]
    congr 1
    exact (List.map_congr_left fun p hp => ih p hp).trans (List.map_id _)

theorem Cls.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (c : Cls) : (c.rsub ρ).rsub ρ = c := by
  cases c <;> simp [Cls.rsub, Ty.rsub_invol hρ]

theorem Pred.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (p : Pred) : (p.rsub ρ).rsub ρ = p := by
  simp [Pred.rsub, Cls.rsub_invol hρ, Function.comp_def, Ty.rsub_invol hρ]

theorem PPred.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (p : PPred) : (p.rsub ρ).rsub ρ = p := by
  simp [PPred.rsub, Cls.rsub_invol hρ, Function.comp_def, PTy.rsub_invol hρ]

theorem Scheme.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (s : Scheme) : (s.rsub ρ).rsub ρ = s := by
  simp [Scheme.rsub, PTy.rsub_invol hρ, Function.comp_def, PPred.rsub_invol hρ]

/-! ## Renaming commutes with substitution -/

/-- A substitution's images renamed. -/
def Subst.rsub (ρ : RSubst) (ψ : Subst) : Subst := ψ.map fun p => (p.1, p.2.rsub ρ)

theorem Subst.rsub_invol {ρ : RSubst} (hρ : ρ.Invol) (ψ : Subst) : Subst.rsub ρ (Subst.rsub ρ ψ) = ψ := by
  simp [Subst.rsub, Function.comp_def, Ty.rsub_invol hρ]

theorem Subst.find_rsub (ρ : RSubst) (ψ : Subst) (a : Nat) :
    (Subst.rsub ρ ψ).find a = (ψ.find a).map (·.rsub ρ) := by
  induction ψ with
  | nil => rfl
  | cons p ψ ih =>
    obtain ⟨b, t⟩ := p
    show Subst.find ((b, t.rsub ρ) :: Subst.rsub ρ ψ) a = _
    simp only [Subst.find]
    split
    · rfl
    · exact ih

theorem RTy.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (r : RTy) :
    (r.subst ψ).rsub ρ = (r.rsub ρ).subst (Subst.rsub ρ ψ) := by
  induction r using RTy.ind with
  | free a =>
    show (((ψ.find a).getD (.var a)).toRTy).rsub ρ = (((Subst.rsub ρ ψ).find a).getD (.var a)).toRTy
    rw [Ty.toRTy_rsub, Subst.find_rsub]
    cases ψ.find a <;> rfl
  | self j => rfl
  | app c args ih =>
    rw [RTy.subst_app, RTy.rsub_app, RTy.rsub_app, Con.rimgA_map]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := Con.rimg_ren hρ hc
      rfl
    | none =>
      simp only [RTy.subst_app, List.map_map]
      congr 1
      exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [RTy.subst_mu, RTy.rsub_mu, List.map_map]
    congr 1
    exact List.map_congr_left ih

theorem Ty.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (τ : Ty) :
    (τ.subst ψ).rsub ρ = (τ.rsub ρ).subst (Subst.rsub ρ ψ) := by
  induction τ using Ty.ind with
  | var a =>
    show ((ψ.find a).getD (.var a)).rsub ρ = ((Subst.rsub ρ ψ).find a).getD (.var a)
    rw [Subst.find_rsub]
    cases ψ.find a <;> rfl
  | app c args ih =>
    rw [Ty.subst_app, Ty.rsub_app, Ty.rsub_app, Con.rimgA_map]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := Con.rimg_ren hρ hc
      rfl
    | none =>
      simp only [Ty.subst_app, List.map_map]
      congr 1
      exact List.map_congr_left ih
  | mu i sys =>
    simp only [Ty.subst_mu, Ty.rsub_mu, List.map_map]
    congr 1
    exact List.map_congr_left fun r _ => RTy.subst_rsub hρ ψ r

theorem PTy.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (p : PTy) :
    (p.subst ψ).rsub ρ = (p.rsub ρ).subst (Subst.rsub ρ ψ) := by
  induction p using PTy.ind with
  | free a =>
    show (((ψ.find a).getD (.var a)).toPTy).rsub ρ = (((Subst.rsub ρ ψ).find a).getD (.var a)).toPTy
    rw [Ty.toPTy_rsub, Subst.find_rsub]
    cases ψ.find a <;> rfl
  | bound i => rfl
  | self j => rfl
  | app c args ih =>
    rw [PTy.subst_app, PTy.rsub_app, PTy.rsub_app, Con.rimgA_map]
    cases h : c.rimgA ρ args with
    | some t =>
      obtain ⟨hc, rfl⟩ := Con.rimgA_some h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := Con.rimg_ren hρ hc
      rfl
    | none =>
      simp only [PTy.subst_app, List.map_map]
      congr 1
      exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [PTy.subst_mu, PTy.rsub_mu, List.map_map]
    congr 1
    exact List.map_congr_left ih

theorem Pred.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (p : Pred) :
    (p.subst ψ).rsub ρ = (p.rsub ρ).subst (Subst.rsub ρ ψ) := by
  simp [Pred.subst, Pred.rsub, Ty.subst_rsub hρ]

theorem PPred.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (p : PPred) :
    (p.subst ψ).rsub ρ = (p.rsub ρ).subst (Subst.rsub ρ ψ) := by
  simp [PPred.subst, PPred.rsub, PTy.subst_rsub hρ]

theorem Scheme.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (s : Scheme) :
    (s.subst ψ).rsub ρ = (s.rsub ρ).subst (Subst.rsub ρ ψ) := by
  simp [Scheme.subst, Scheme.rsub, PTy.subst_rsub hρ, PPred.subst_rsub hρ]

theorem Ctx.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (Γ : Ctx) :
    (Ctx.subst ψ Γ).map (Scheme.rsub ρ) = Ctx.subst (Subst.rsub ρ ψ) (Γ.map (Scheme.rsub ρ)) := by
  simp [Ctx.subst, Scheme.subst_rsub hρ]

theorem Ret.subst_rsub {ρ : RSubst} (hρ : ρ.Renaming) (ψ : Subst) (R : Option Ty) :
    (Ret.subst ψ R).map (·.rsub ρ) = Ret.subst (Subst.rsub ρ ψ) (R.map (·.rsub ρ)) := by
  cases R <;> simp [Ret.subst, Ty.subst_rsub hρ]

end Inty
