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
  rcases hs q hq with ⟨i, hi, h | ⟨l, τ, h⟩⟩ | ⟨q', τ, t, r, h, hb⟩ <;> subst h
  · exact .inl ⟨i, hi, .inl (by simp [PPred.subst, PTy.subst])⟩
  · exact .inl ⟨i, hi, .inr ⟨l, τ.subst σ, by simp [PPred.subst, PTy.subst]⟩⟩
  · exact .inr ⟨q'.subst σ, τ.subst σ, t.subst σ, r.subst σ, by simp [PPred.subst],
      by simpa [Scheme.subst] using hb⟩

theorem objSlots_subst (σ : Subst) (L ls : List String) (τs absent : List Ty) :
    (objSlots L ls τs absent).map (·.subst σ) =
      objSlots L ls (τs.map (·.subst σ)) (absent.map (·.subst σ)) := by
  simp only [objSlots, List.map_map, ← List.map_reverse, Ty.field_subst]
  rw [List.zip_map_right, List.map_map]
  apply List.map_congr_left
  intro p _
  obtain ⟨l, τa⟩ := p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  generalize Ty.field l ls.reverse τs.reverse = o
  cases o <;> simp

theorem HasType.subst (σ : Subst) (h : HasType L C Γ R e τ) :
    HasType L (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) e (τ.subst σ) := by
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
  | let_ s F _ hv hs _ ih₁ ih₂ =>
    refine .let_ (s.subst σ) (F ++ σ.map Prod.fst) (fun m hm => ?_) ?_ ?_ (by simpa using ih₂)
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
  | obj hτs habs hL hes _ ih =>
    simp only [Ty.subst_app, objSlots_subst]
    refine .obj (by simpa using hτs) (by simpa using habs) hL hes (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq
  | get _ hp ih => exact .get ih (by simpa [Pred.subst] using hp.subst σ)
  | set _ hp _ ihe ihv => exact .set ihe (by simpa [Pred.subst] using hp.subst σ) ihv
  | @spread _ _ _ _ _ _ ps τs _ hps hτs hss hrs _ _ hm ih₁ ih₂ =>
    simp only [Ty.subst_app] at ih₁ ih₂ ⊢
    refine .spread (ps := ps.map (·.subst σ)) (τs := τs.map (·.subst σ))
      (by simpa using hps) (by simpa using hτs) (by simpa using hss) (by simpa using hrs) ih₁ ?_
      (fun p hp => ?_)
    · simpa [List.map_zipWith, List.zipWith_map] using ih₂
    · rw [← mergePreds_subst] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hm q hq).subst σ

end Inty
