import Inty.Typing

/-!
# Typing is preserved by type substitution

If `e` has type `τ` under `C` and `Γ`, it has `τ.subst σ` under `C` and `Γ`
with every type and scheme substituted. This is what lets a generalised
`const` be used at every instance of its scheme: the soundness proof types
its initialiser at fresh variables, then substitutes the instance's types
for them.
-/

namespace Inty

theorem PlusInst.subst (σ : Subst) (h : PlusInst τ) : PlusInst (τ.subst σ) := by
  cases h <;> constructor

theorem Entails.subst (σ : Subst) (h : Entails C τ) :
    Entails (C.map (·.subst σ)) (τ.subst σ) :=
  h.elim (fun h => .inl (h.subst σ)) (fun h => .inr (List.mem_map_of_mem h))

theorem HasType.subst (σ : Subst) (h : HasType C Γ R e τ) :
    HasType (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) e (τ.subst σ) := by
  induction h with
  | lit hl => cases hl <;> exact .lit (by constructor)
  | var hi hlen hc =>
    rw [Scheme.inst_subst]
    refine .var (by simp [List.getElem?_map, hi]) (by simpa [Scheme.subst] using hlen) ?_
    intro c hc'
    rw [← Scheme.instPlus_subst] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
    exact (hc c₀ hc₀).subst σ
  | func _ ih => exact .func (by simpa [Ty.subst] using ih)
  | app _ _ ihf iha => exact .app (by simpa [Ty.subst] using ihf) iha
  | let_ s L _ hv _ ih₁ ih₂ =>
    refine .let_ (s.subst σ) (L ++ σ.map Prod.fst) (fun m hm => ?_) ?_ (by simpa using ih₂)
    · have hσ : ∀ p ∈ σ, p.1 < m := fun p hp => hm p.1 (by simp; exact .inr ⟨_, hp⟩)
      rw [← Scheme.open_subst s hσ, ← Scheme.openPlus_subst s hσ, ← List.map_append]
      exact ih₁ m (fun a ha => hm a (by simp [ha]))
    · simpa [Scheme.subst] using hv
  | cond _ _ _ ihc iht ihe => exact .cond ihc iht ihe
  | unop hop _ ih =>
    cases hop with
    | not => exact .unop .not ih
    | typeof => exact .unop .typeof ih
    | neg => exact .unop .neg ih
  | binop hop _ _ ih₁ ih₂ =>
    cases hop with
    | plus hc => exact .binop (.plus (hc.subst σ)) ih₁ ih₂
    | minus => exact .binop .minus ih₁ ih₂
  | ret _ ih => exact .ret ih
  | throw_ _ ih => exact .throw_ ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂

end Inty
