import Inty.InferInv

/-!
# Rigid type variables under substitution and renaming

What completeness with polymorphic annotations needs of rigid type
variables: a substitution adds to a type only the rigid variables of the
types it substitutes (`Ty.rkeys_subst`), and swapping two rigid names keeps
equal schemes and contexts equal (`CtxEq.rsub`).
-/

namespace Inty

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l <;> simp_all

theorem RTy.rkeys_toPTy (r : RTy) : r.toPTy.rkeys = r.rkeys := by
  induction r using RTy.ind with
  | free a => rfl
  | self j => rfl
  | app c args ih =>
    simp only [RTy.toPTy_app, PTy.rkeys, RTy.rkeys, PTy.rkeysL_eq, RTy.rkeysL_eq,
      List.flatMap_map]
    congr 1
    exact flatMap_congr' ih
  | mu i sys ih =>
    simp only [RTy.toPTy, RTy.toPTys_eq, PTy.rkeys, RTy.rkeys, PTy.rkeysL_eq, RTy.rkeysL_eq,
      List.flatMap_map]
    exact flatMap_congr' ih

theorem Ty.rkeys_toRTy (τ : Ty) : τ.toRTy.rkeys = τ.rkeys := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toRTy_app, RTy.rkeys, Ty.rkeys, RTy.rkeysL_eq, Ty.rkeysL_eq, List.flatMap_map]
    congr 1
    exact flatMap_congr' ih
  | mu i sys => rfl

theorem Ty.rkeys_toPTy (τ : Ty) : τ.toPTy.rkeys = τ.rkeys := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toPTy_app, PTy.rkeys, Ty.rkeys, PTy.rkeysL_eq, Ty.rkeysL_eq, List.flatMap_map]
    congr 1
    exact flatMap_congr' ih
  | mu i sys =>
    simp only [Ty.toPTy, RTy.toPTys_eq, PTy.rkeys, Ty.rkeys, PTy.rkeysL_eq, RTy.rkeysL_eq,
      List.flatMap_map]
    exact flatMap_congr' fun r _ => RTy.rkeys_toPTy r

/-- A rigid variable of a substituted type is one of the type's, or of what
the substitution gives one of its variables. -/
theorem RTy.rkeys_subst {σ : Subst} {k : Nat} {r : RTy} (h : k ∈ (r.subst σ).rkeys) :
    k ∈ r.rkeys ∨ ∃ b ∈ r.ftv, k ∈ ((Ty.var b).subst σ).rkeys := by
  induction r using RTy.ind with
  | free a =>
    simp only [RTy.subst, Ty.rkeys_toRTy] at h
    exact .inr ⟨a, by simp [RTy.ftv], h⟩
  | self j => simp [RTy.subst, RTy.rkeys] at h
  | app c args ih =>
    simp only [RTy.subst_app, RTy.rkeys, RTy.rkeysL_eq, List.flatMap_map, List.mem_append,
      List.mem_flatMap] at h
    rcases h with h | ⟨p, hp, h⟩
    · exact .inl (by simp [RTy.rkeys, h])
    · rcases ih p hp h with h | ⟨b, hb, h⟩
      · refine .inl ?_
        simp only [RTy.rkeys, RTy.rkeysL_eq, List.mem_append, List.mem_flatMap]
        exact .inr ⟨p, hp, h⟩
      · exact .inr ⟨b, by simp only [RTy.ftv, RTy.ftvs_eq, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩
  | mu i sys ih =>
    simp only [RTy.subst_mu, RTy.rkeys, RTy.rkeysL_eq, List.flatMap_map, List.mem_flatMap] at h
    obtain ⟨p, hp, h⟩ := h
    rcases ih p hp h with h | ⟨b, hb, h⟩
    · exact .inl (by simp only [RTy.rkeys, RTy.rkeysL_eq, List.mem_flatMap]; exact ⟨p, hp, h⟩)
    · exact .inr ⟨b, by simp only [RTy.ftv, RTy.ftvs_eq, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩

theorem Ty.rkeys_subst {σ : Subst} {k : Nat} {τ : Ty} (h : k ∈ (τ.subst σ).rkeys) :
    k ∈ τ.rkeys ∨ ∃ b ∈ τ.ftv, k ∈ ((Ty.var b).subst σ).rkeys := by
  induction τ using Ty.ind with
  | var a => exact .inr ⟨a, by simp [Ty.ftv], h⟩
  | app c args ih =>
    simp only [Ty.subst_app, Ty.rkeys, Ty.rkeysL_eq, List.flatMap_map, List.mem_append,
      List.mem_flatMap] at h
    rcases h with h | ⟨p, hp, h⟩
    · exact .inl (by simp [Ty.rkeys, h])
    · rcases ih p hp h with h | ⟨b, hb, h⟩
      · refine .inl ?_
        simp only [Ty.rkeys, Ty.rkeysL_eq, List.mem_append, List.mem_flatMap]
        exact .inr ⟨p, hp, h⟩
      · exact .inr ⟨b, by simp only [Ty.ftv, Ty.ftvs_eq, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩
  | mu i sys =>
    simp only [Ty.subst_mu, Ty.rkeys, RTy.rkeysL_eq, List.flatMap_map, List.mem_flatMap] at h
    obtain ⟨p, hp, h⟩ := h
    rcases RTy.rkeys_subst h with h | ⟨b, hb, h⟩
    · exact .inl (by simp only [Ty.rkeys, RTy.rkeysL_eq, List.mem_flatMap]; exact ⟨p, hp, h⟩)
    · exact .inr ⟨b, by simp only [Ty.ftv, RTy.ftvs_eq, List.mem_flatMap]; exact ⟨p, hp, hb⟩, h⟩

theorem PTy.rkeys_subst {σ : Subst} {k : Nat} {p : PTy} (h : k ∈ (p.subst σ).rkeys) :
    k ∈ p.rkeys ∨ ∃ b ∈ p.ftv, k ∈ ((Ty.var b).subst σ).rkeys := by
  induction p using PTy.ind with
  | free a =>
    simp only [PTy.subst, Ty.rkeys_toPTy] at h
    exact .inr ⟨a, by simp [PTy.ftv], h⟩
  | bound i => simp [PTy.subst, PTy.rkeys] at h
  | self j => simp [PTy.subst, PTy.rkeys] at h
  | app c args ih =>
    simp only [PTy.subst_app, PTy.rkeys, PTy.rkeysL_eq, List.flatMap_map, List.mem_append,
      List.mem_flatMap] at h
    rcases h with h | ⟨q, hq, h⟩
    · exact .inl (by simp [PTy.rkeys, h])
    · rcases ih q hq h with h | ⟨b, hb, h⟩
      · refine .inl ?_
        simp only [PTy.rkeys, PTy.rkeysL_eq, List.mem_append, List.mem_flatMap]
        exact .inr ⟨q, hq, h⟩
      · exact .inr ⟨b, by simp only [PTy.ftv, PTy.ftvs_eq, List.mem_flatMap]; exact ⟨q, hq, hb⟩, h⟩
  | mu i sys ih =>
    simp only [PTy.subst_mu, PTy.rkeys, PTy.rkeysL_eq, List.flatMap_map, List.mem_flatMap] at h
    obtain ⟨q, hq, h⟩ := h
    rcases ih q hq h with h | ⟨b, hb, h⟩
    · exact .inl (by simp only [PTy.rkeys, PTy.rkeysL_eq, List.mem_flatMap]; exact ⟨q, hq, h⟩)
    · exact .inr ⟨b, by simp only [PTy.ftv, PTy.ftvs_eq, List.mem_flatMap]; exact ⟨q, hq, hb⟩, h⟩

theorem Scheme.rkeys_subst {σ : Subst} {k : Nat} {s : Scheme} (h : k ∈ (s.subst σ).rkeys) :
    k ∈ s.rkeys ∨ ∃ b ∈ s.ftv, k ∈ ((Ty.var b).subst σ).rkeys := by
  obtain ⟨n, body, ps⟩ := s
  simp only [Scheme.subst, Scheme.rkeys, List.flatMap_map, List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨p, hp, h⟩
  · rcases PTy.rkeys_subst h with h | ⟨b, hb, h⟩
    · exact .inl (by simp [Scheme.rkeys, h])
    · exact .inr ⟨b, by simp [Scheme.ftv, hb], h⟩
  · simp only [PPred.subst, PPred.rkeys, PTy.rkeysL_eq, List.flatMap_map, List.mem_append,
      List.mem_flatMap] at h
    rcases h with h | ⟨q, hq, h⟩
    · exact .inl (by
        simp only [Scheme.rkeys, List.mem_append, List.mem_flatMap]
        exact .inr ⟨p, hp, by simp [PPred.rkeys, h]⟩)
    · rcases PTy.rkeys_subst h with h | ⟨b, hb, h⟩
      · exact .inl (by
          simp only [Scheme.rkeys, List.mem_append, List.mem_flatMap]
          exact .inr ⟨p, hp, by
            simp only [PPred.rkeys, PTy.rkeysL_eq, List.mem_append, List.mem_flatMap]
            exact .inr ⟨q, hq, h⟩⟩)
      · exact .inr ⟨b, by
          simp only [Scheme.ftv, List.mem_append, List.mem_flatMap]
          exact .inr ⟨p, hp, by simp only [PPred.ftv, List.mem_flatMap]; exact ⟨q, hq, hb⟩⟩, h⟩

theorem ctxRkeys_subst {σ : Subst} {k : Nat} {Γ : Ctx} (h : k ∈ ctxRkeys (Ctx.subst σ Γ)) :
    k ∈ ctxRkeys Γ ∨ ∃ b ∈ ctxFtv Γ, k ∈ ((Ty.var b).subst σ).rkeys := by
  simp only [ctxRkeys, Ctx.subst, List.flatMap_map, List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  rcases Scheme.rkeys_subst h with h | ⟨b, hb, h⟩
  · exact .inl (List.mem_flatMap.mpr ⟨s, hs, h⟩)
  · exact .inr ⟨b, List.mem_flatMap.mpr ⟨s, hs, hb⟩, h⟩

theorem Ret.rkeys_subst {σ : Subst} {k : Nat} {R : Option Ty} (h : k ∈ Ret.rkeys (Ret.subst σ R)) :
    k ∈ Ret.rkeys R ∨ ∃ b ∈ Ret.ftv R, k ∈ ((Ty.var b).subst σ).rkeys := by
  cases R with
  | none => simp [Ret.rkeys, Ret.subst] at h
  | some τ =>
    simp only [Ret.rkeys, Ret.subst, Option.map_some, Option.getD_some] at h
    simpa [Ret.rkeys, Ret.ftv] using Ty.rkeys_subst h

/-! ## Renaming equal schemes -/

theorem SchemeEq.rsub {ρ : RSubst} (hρ : ρ.Invol) {s s' : Scheme} (h : SchemeEq s s') :
    SchemeEq (s.rsub ρ) (s'.rsub ρ) := by
  obtain ⟨ha, hl, he⟩ := h
  refine ⟨by simpa [Scheme.rsub] using ha, by simpa [Scheme.rsub] using hl, fun τs hτs => ?_⟩
  have hinv : (τs.map (·.rsub ρ)).map (·.rsub ρ) = τs := by
    simp only [List.map_map]
    exact (List.map_congr_left fun τ _ => Ty.rsub_invol hρ τ).trans (List.map_id _)
  obtain ⟨h₁, h₂⟩ := he (τs.map (·.rsub ρ)) (by simpa [Scheme.rsub] using hτs)
  rw [← hinv, Scheme.inst_rsub, Scheme.inst_rsub, Scheme.instPreds_rsub, Scheme.instPreds_rsub]
  refine ⟨TyEq.rsub ρ h₁, fun x hx => ?_⟩
  rw [List.zip_map] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact PredEq.rsub ρ (h₂ y hy)

theorem CtxEq.rsub {ρ : RSubst} (hρ : ρ.Invol) {Γ Γ' : Ctx} (h : CtxEq Γ Γ') :
    CtxEq (Γ.map (Scheme.rsub ρ)) (Γ'.map (Scheme.rsub ρ)) := by
  refine ⟨by simpa using h.1, fun i s s' hs hs' => ?_⟩
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hs hs'
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨t', ht', rfl⟩ := hs'
  exact (h.2 i t t' ht ht').rsub hρ

theorem RetEq.rsub (ρ : RSubst) : ∀ {R R' : Option Ty}, RetEq R R' →
    RetEq (R.map (·.rsub ρ)) (R'.map (·.rsub ρ))
  | none, none, _ => trivial
  | some _, some _, h => TyEq.rsub ρ h

end Inty
