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

theorem Scheme.Simple.subst {s : Scheme} (hs : s.Simple) (σ : Subst) : (s.subst σ).Simple := by
  intro p hp
  simp only [Scheme.subst, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨i, hi, rfl⟩ := hs q hq
  exact ⟨i, hi, by simp [PPred.subst, PTy.subst]⟩

theorem HasType.subst (σ : Subst) (h : HasType C Γ R e τ) :
    HasType (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) e (τ.subst σ) := by
  induction h with
  | lit hl => cases hl <;> exact .lit (by constructor)
  | var hi hlen hc =>
    rw [Scheme.inst_subst]
    refine .var (by simp [List.getElem?_map, hi]) (by simpa [Scheme.subst] using hlen) ?_
    intro c hc'
    rw [← Scheme.instPreds_subst] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
    exact (hc c₀ hc₀).subst σ
  | func hlen _ ih =>
    refine .func (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def] using ih
  | app _ hlen _ ihf iha =>
    refine .app (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | let_ s L _ hv hs _ ih₁ ih₂ =>
    refine .let_ (s.subst σ) (L ++ σ.map Prod.fst) (fun m hm => ?_) ?_ ?_ (by simpa using ih₂)
    · have hσ : ∀ p ∈ σ, p.1 < m := fun p hp => hm p.1 (by simp; exact .inr ⟨_, hp⟩)
      rw [← Scheme.open_subst s hσ, ← Scheme.openPreds_subst s hσ, ← List.map_append]
      exact ih₁ m (fun a ha => hm a (by simp [ha]))
    · simpa [Scheme.subst] using hv
    · exact hs.subst σ
  | assign hi ha hp _ ih =>
    rw [Scheme.inst_subst]
    refine .assign (by simp [List.getElem?_map, hi]) (by simpa [Scheme.subst] using ha)
      (by simp [Scheme.subst, hp]) ?_
    simpa [Scheme.inst_subst] using ih
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
  | while_ _ _ ihc ihb => exact .while_ ihc ihb
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch _ _ ihb ihh => exact .tryCatch ihb (by simpa using ihh)
  | tryFinally _ _ ihb ihf => exact .tryFinally ihb ihf

end Inty
