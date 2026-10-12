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

/-! ## Rigid variables in a type's tree

Equal types can differ in their rigid variables, as in their type variables,
where a recursive type's system has an equation its unfolding never reaches.
`Ty.TreeRk k τ`: the rigid variable `k` is a leaf of the tree `τ` unfolds to,
which equal types agree on. -/

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

/-- A leaf `k` of a type with `k'` and `k` swapped was a leaf `k'`. -/
theorem Ty.treeRk_swap {k k' : Nat} (hne : k ≠ k') :
    ∀ {n : Nat} {τ : Ty}, ((τ.approx n).graftR (RSubst.swap k' k) n).HasRk k → (τ.approx n).HasRk k'
  | 0, _, h => by cases h
  | n + 1, τ, h => by
    rw [Ty.approx_succ] at h ⊢
    split at h
    · cases h
    · rename_i c args _
      simp only [Tree.graftR, Con.rimgA_map] at h
      split at h
      · rename_i τ' hc
        obtain ⟨hc, rfl⟩ := Con.rimgA_some hc
        clear ‹Con.rimgA _ _ [] = some _›
        cases c with
        | rigid s i =>
          simp only [Con.rimg, RSubst.swap] at hc
          by_cases hs : s = k'
          · subst hs; exact .here (by simp [Con.rkeys]) rfl
          · by_cases hs' : s = k
            · simp [hs', hne] at hc
              subst hc
              simp only [Ty.approx_succ, Ty.view, List.map_nil] at h
              cases h with
              | here hk _ => simp [Con.rkeys] at hk; exact absurd hk hne
              | under ht _ => cases ht
            · simp [hs, hs'] at hc
        | _ => simp [Con.rimg] at hc
      · rename_i hc
        cases h with
        | here hk he =>
          exfalso
          cases c with
          | rigid s i =>
            simp only [Con.rkeys, List.mem_singleton] at hk
            subst hk
            simp only [List.map_eq_nil_iff] at he
            subst he
            simp only [Con.rimgA, List.isEmpty_nil, ite_true, Con.rimg, RSubst.swap] at hc
            split at hc <;> simp at hc
          | _ => simp [Con.rkeys] at hk
        | under ht hh =>
          simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
          obtain ⟨a, ha, rfl⟩ := ht
          exact .under (List.mem_map.mpr ⟨a, ha, rfl⟩) (Ty.treeRk_swap hne hh)
    · cases h

theorem Ty.TreeRk.of_swap {k k' : Nat} (hne : k ≠ k') {τ : Ty}
    (h : (τ.rsub (RSubst.swap k' k)).TreeRk k) : τ.TreeRk k' := by
  obtain ⟨n, hn⟩ := h
  rw [Ty.approx_rsub] at hn
  exact ⟨n, Ty.treeRk_swap hne hn⟩

theorem Tree.graftR_swap_off {k k' : Nat} :
    ∀ {n : Nat} {τ : Ty}, ¬ (τ.approx n).HasRk k → ¬ (τ.approx n).HasRk k' →
      (τ.approx n).graftR (RSubst.swap k' k) n = τ.approx n
  | 0, _, _, _ => rfl
  | n + 1, τ, h, h' => by
    rw [Ty.approx_succ] at h h' ⊢
    split at h
    · rfl
    · rename_i c args hv
      simp only [hv] at h'
      simp only [Tree.graftR, Con.rimgA_map]
      split
      · rename_i τ' hc
        exfalso
        obtain ⟨hc, rfl⟩ := Con.rimgA_some hc
        clear ‹Con.rimgA _ _ [] = some _›
        cases c with
        | rigid s i =>
          simp only [Con.rimg, RSubst.swap] at hc
          by_cases hs : s = k'
          · subst hs; exact h' (.here (by simp [Con.rkeys]) rfl)
          · by_cases hs' : s = k
            · subst hs'; exact h (.here (by simp [Con.rkeys]) rfl)
            · simp [hs, hs'] at hc
        | _ => simp [Con.rimg] at hc
      · congr 1
        rw [List.map_map]
        refine List.map_congr_left fun a ha => Tree.graftR_swap_off
          (fun hh => h (.under (List.mem_map.mpr ⟨a, ha, rfl⟩) hh))
          (fun hh => h' (.under (List.mem_map.mpr ⟨a, ha, rfl⟩) hh))
    · rfl

/-- Swapping two names a type's tree has no leaf of leaves it equal. -/
theorem Ty.rsub_swap_tyEq {k k' : Nat} {τ : Ty} (h : ¬ τ.TreeRk k) (h' : ¬ τ.TreeRk k') :
    TyEq (τ.rsub (RSubst.swap k' k)) τ := fun n => by
  rw [Ty.approx_rsub]
  exact Tree.graftR_swap_off (fun hn => h ⟨n, hn⟩) (fun hn => h' ⟨n, hn⟩)

end Inty
