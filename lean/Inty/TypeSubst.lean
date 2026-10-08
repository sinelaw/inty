import Inty.Typing

/-!
# Typing is preserved by type substitution

If `e` has type `τ` in `Γ`, it has `τ.subst σ` in `Γ` with every scheme
substituted. This is what lets a generalised `const` be used at every
instance of its scheme: the soundness proof types its initialiser at fresh
variables, then substitutes the instance's types for them.
-/

namespace Inty

theorem HasType.subst (σ : Subst) (h : HasType Γ e τ) :
    HasType (Γ.map (Scheme.subst σ)) e (τ.subst σ) := by
  induction h with
  | lit hl => cases hl <;> exact .lit (by constructor)
  | var hi hlen =>
    rw [Scheme.inst_subst]
    exact .var (by simp [List.getElem?_map, hi]) (by simpa [Scheme.subst] using hlen)
  | func _ ih => exact .func (by simpa [Ty.subst] using ih)
  | app _ _ ihf iha => exact .app (by simpa [Ty.subst] using ihf) iha
  | let_ s L _ hv _ ih₁ ih₂ =>
    refine .let_ (s.subst σ) (L ++ σ.map Prod.fst) (fun m hm => ?_) hv (by simpa using ih₂)
    have hσ : ∀ p ∈ σ, p.1 < m := fun p hp => hm p.1 (by simp; exact .inr ⟨_, hp⟩)
    rw [← Scheme.open_subst s hσ]
    exact ih₁ m (fun a ha => hm a (by simp [ha]))
  | cond _ _ _ ihc iht ihe => exact .cond ihc iht ihe
  | unop hop _ ih =>
    cases hop with
    | not => exact .unop .not ih
    | typeof => exact .unop .typeof ih
    | neg => exact .unop .neg ih
  | binop hop _ _ ih₁ ih₂ =>
    cases hop with
    | plus hc => cases hc <;> exact .binop (.plus (by constructor)) ih₁ ih₂
    | minus => exact .binop .minus ih₁ ih₂

end Inty
