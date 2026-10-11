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
  rcases hs q hq with ⟨hcls, hlen, i, hi, rest, h⟩ | ⟨q', k, τ, t, r, h, hb⟩
  · refine .inl ⟨hcls, by simpa [PPred.subst] using hlen, i, hi, rest.map (·.subst σ), ?_⟩
    simp [PPred.subst, h, PTy.subst]
  · subst h
    obtain ⟨i, hi, x, hx, hb⟩ := hb
    refine .inr ⟨q'.subst σ, k.subst σ, τ.subst σ, t.subst σ, r.subst σ, by simp [PPred.subst],
      i, by simpa [Scheme.subst] using hi, x.subst σ, ?_, by simpa using hb.subst hi σ⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem objSlots_subst (σ : Subst) (L ls : List String) (ss : List Ty) :
    (objSlots L ls ss).map (·.subst σ) = objSlots L ls (ss.map (·.subst σ)) := by
  simp only [objSlots, List.map_map, ← List.map_reverse, Ty.field_subst]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  generalize Ty.field l ls.reverse ss.reverse = o
  cases o <;> simp [Ty.subst]

theorem FieldSlot.subst (σ : Subst) (h : FieldSlot T k e τ s) :
    FieldSlot (T.subst σ) k e (τ.subst σ) (s.subst σ) := by
  cases h with
  | data => exact .data
  | method he => simpa using FieldSlot.method (τs := _) (ρ := _) (he.subst σ)
  | getter he => simpa using FieldSlot.getter (σ := _) (he.subst σ)

theorem MemberSlot.subst (σ : Subst) (h : MemberSlot T k e τ s) :
    MemberSlot (T.subst σ) k e (τ.subst σ) (s.subst σ) := by
  cases h with
  | data => exact .data
  | arrow he => simpa using MemberSlot.arrow (τs := _) (ρ := _) (θ' := _) (he.subst σ)
  | method he => simpa using MemberSlot.method (τs := _) (ρ := _) (he.subst σ)
  | getter he => simpa using MemberSlot.getter (σ := _) (he.subst σ)

theorem memberCtx_subst (σ : Subst) (Γ : Ctx) (ks : List ClassKind) (τs : List Ty)
    (i : Nat) (k : ClassKind) :
    (memberCtx Γ ks τs i k).map (Scheme.subst σ) =
      memberCtx (Γ.map (Scheme.subst σ)) ks (τs.map (·.subst σ)) i k := by
  cases k with
  | data =>
    simp only [memberCtx, List.map_append]
    congr 1
    rw [List.zip_map_right, ← List.map_take]
    generalize (ks.zip τs).take i = xs
    induction xs with
    | nil => rfl
    | cons p ps ih =>
      obtain ⟨k, τ⟩ := p
      cases k <;> simp_all [Scheme.mono, Scheme.subst]
  | arrow => rfl
  | method => rfl
  | getter => rfl

theorem zip4_map {α δ β γ : Type} (f : β → β) (g : γ → γ) : ∀ (ks : List α) (es : List δ)
    (τs : List β) (ss : List γ), ks.zip (es.zip ((τs.map f).zip (ss.map g))) =
      (ks.zip (es.zip (τs.zip ss))).map (fun x => (x.1, x.2.1, f x.2.2.1, g x.2.2.2))
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: _, _ :: _, _ :: _, [] => rfl
  | k :: ks, e :: es, t :: ts, s :: ss => by simp [zip4_map f g ks es ts ss]

theorem zip3_map {α β γ : Type} (f : β → β) (g : γ → γ) : ∀ (ks : List α) (τs : List β) (ss : List γ),
    ks.zip ((τs.map f).zip (ss.map g)) = (ks.zip (τs.zip ss)).map (fun x => (x.1, f x.2.1, g x.2.2))
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | k :: ks, t :: ts, s :: ss => by simp [zip3_map f g ks ts ss]

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
  | @obj _ _ _ _ _ _ _ τs hes hks hτs hss hL _ hm ih =>
    simp only [Ty.subst_app, objSlots_subst]
    refine .obj (τs := τs.map (·.subst σ)) hes hks (by simpa using hτs) (by simpa using hss) hL (fun p hp => ?_) (fun x hx => ?_)
    · rw [List.zip_map_right] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
    · rw [zip4_map] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).subst σ
      simpa [Ty.subst_app, objSlots_subst] using this
  | @cls _ _ _ τs _ _ _ _ hes hks hτs hss hnd hL _ hm ih =>
    simp only [Ty.subst_app, objSlots_subst]
    refine .cls (τs := τs.map (·.subst σ)) hes hks (by simpa using hτs) (by simpa using hss) hnd hL
      (fun i e k τ he hk hτ => ?_) (fun x hx => ?_)
    · rw [List.getElem?_map] at hτ
      obtain ⟨τ₀, hτ₀, rfl⟩ := Option.map_eq_some_iff.mp hτ
      have := ih i e k τ₀ he hk hτ₀
      rw [memberCtx_subst] at this
      simpa [Ty.subst_app, objSlots_subst] using this
    · rw [zip4_map] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).subst σ
      simpa [Ty.subst_app, objSlots_subst] using this
  | ctor hlen _ ih =>
    refine .ctor (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def] using ih
  | new_ _ hlen _ hρ ihf iha =>
    refine .new_ (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_) (by simpa using hρ.subst σ)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | get _ hp ih => exact .get ih (by simpa [Pred.subst] using hp.subst σ)
  | set _ hp _ ihe ihv => exact .set ihe (by simpa [Pred.subst] using hp.subst σ) ihv
  | @spread _ _ _ _ _ _ ps ks τs _ hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    simp only [Ty.subst_app] at ih₁ ih₂ ⊢
    refine .spread (ps := ps.map (·.subst σ)) (ks := ks.map (·.subst σ)) (τs := τs.map (·.subst σ))
      (by simpa using hps) (by simpa using hks) (by simpa using hτs) (by simpa using hss)
      (by simpa using hrs) ih₁ ?_ (fun p hp => ?_)
    · simpa [slots3_subst] using ih₂
    · rw [← mergePreds_subst] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hm q hq).subst σ
  | arr _ ih => exact .arr ih
  | index _ _ hp ihe ihi => exact .index ihe ihi (by simpa [Pred.subst] using hp.subst σ)
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    exact .setIndex ihe ihi (by simpa [Pred.subst] using hp.subst σ)
      (by simpa [Pred.subst] using hw.subst σ) ihv
  | mcall _ hp hlen _ ihe iha =>
    refine .mcall ihe (by simpa [Pred.subst] using hp.subst σ) (by simpa using hlen)
      (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | conv _ he ih => exact .conv ih (he.subst σ)

end Inty
