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

/-! ## Heads through substitution, up to equal types -/

/-- A type whose image is equal to a constructor application unfolds to a
variable or to that constructor. -/
theorem Ty.whnf_app_of_tyEq {t : Ty} {φ : Subst} {c : Con} {ys : List Ty}
    (h : TyEq (t.subst φ) (.app c ys)) :
    (∃ a, t.whnf = .var a) ∨ ∃ xs, t.whnf = .app c xs ∧ xs.length = ys.length ∧
      ∀ x ∈ xs.zip ys, TyEq (x.1.subst φ) x.2 := by
  obtain ⟨zs, hz, he⟩ := TyEq.whnf_app h.symm rfl
  rcases Ty.whnf_subst_app hz with ⟨a, ha⟩ | ⟨xs, hxs, rfl⟩
  · exact .inl ⟨a, ha⟩
  · obtain ⟨-, hl, hzz⟩ := TyEq.app_iff.mp he
    refine .inr ⟨xs, hxs, by simpa using hl.symm, fun x hx => ?_⟩
    obtain ⟨u, v⟩ := x
    have : (v, u.subst φ) ∈ ys.zip (xs.map (·.subst φ)) := by
      rw [List.zip_map_right]
      exact List.mem_map.mpr ⟨(v, u), zip_symm_mem hx, rfl⟩
    exact (hzz _ this).symm

theorem Ty.whnf_con_of_tyEq {t : Ty} {φ : Subst} {c : Con} (h : TyEq (t.subst φ) (.app c [])) :
    (∃ a, t.whnf = .var a) ∨ t.whnf = .app c [] := by
  rcases Ty.whnf_app_of_tyEq h with h | ⟨xs, hxs, hl, -⟩
  · exact .inl h
  · exact .inr (by rw [hxs, List.eq_nil_of_length_eq_zero hl])

theorem Ty.whnf_var_of_tyEq {t : Ty} {φ : Subst} {a : Nat} (h : TyEq (t.subst φ) (.var a)) :
    ∃ b, t.whnf = .var b :=
  Ty.whnf_subst_var (TyEq.whnf_var h.symm rfl)


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

theorem MemberSlotS.subst {S : Sys} (hS : S.Substable) (σ : Subst) (h : MemberSlotS S C T k e τ s) :
    MemberSlotS S (C.map (·.subst σ)) (T.subst σ) k e (τ.subst σ) (s.subst σ) := by
  cases h with
  | data => exact .data
  | arrow he hn =>
    simpa using MemberSlotS.arrow (τs := _) (ρ := _) (he.subst σ)
      (by simpa [Pred.subst] using hn.substS hS σ)
  | method he => simpa using MemberSlotS.method (τs := _) (ρ := _) (he.subst σ)
  | getter he => simpa using MemberSlotS.getter (σ := _) (he.subst σ)

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

@[simp] theorem rigids_subst (σ : Subst) (k n : Nat) : (rigids k n).map (·.subst σ) = rigids k n := by
  simp [rigids, Function.comp_def]

theorem varBlock_subst_fresh {σ : Subst} {m : Nat} (h : ∀ p ∈ σ, p.1 < m) (j : Nat) :
    (varBlock m j).map (·.subst σ) = varBlock m j := by
  simp only [varBlock, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have : σ.find i = none := Subst.find_none fun p hp e => by
    have := h p hp; have := (List.mem_range'.mp hi); omega
  simp [Ty.subst, this]

theorem Ret.tv_subst_nil {σ : Subst} {R : Option Ty} (h : (R.map Ty.tv).getD [] = []) :
    ((R.map (·.subst σ)).map Ty.tv).getD [] = [] := by
  cases R with
  | none => rfl
  | some τr => simpa using Ty.tv_subst_nil (σ := σ) (by simpa using h)

theorem Ty.dataField_subst {T : Ty} {l : String} {τ : Ty} (h : T.dataField l = some τ)
    (σ : Subst) : (T.subst σ).dataField l = some (τ.subst σ) := by
  unfold Ty.dataField at h ⊢
  split at h
  · rename_i ls slots hT
    rw [Ty.whnf_subst_of_app hT σ]
    simp only
    rw [Ty.field_subst]
    split at h
    · rename_i s hs
      rw [hs]
      simp only [Option.map_some]
      split at h
      · rename_i p k τ' hsw
        rw [Ty.whnf_subst_of_app hsw σ]
        simp only [List.map_cons, List.map_nil]
        split at h
        · rename_i hpk
          obtain ⟨hp, hk⟩ := hpk
          rw [Ty.whnf_subst_of_app hp σ, Ty.whnf_subst_of_app hk σ]
          simp only [List.map_nil, and_self, ↓reduceIte]
          simp only [Option.some.injEq] at h ⊢
          rw [h]
        · cases h
      · cases h
    · cases h
  · cases h

theorem Ty.dataFields_subst {T : Ty} (σ : Subst) : ∀ {ls : List String} {τs : List Ty},
    T.dataFields ls = some τs → (T.subst σ).dataFields ls = some (τs.map (·.subst σ))
  | [], τs, h => by
    simp only [Ty.dataFields, Option.some.injEq] at h ⊢
    subst h; rfl
  | l :: ls, τs, h => by
    simp only [Ty.dataFields] at h ⊢
    split at h
    · rename_i τ τs' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      rw [Ty.dataField_subst h1 σ, Ty.dataFields_subst σ h2]
      rfl
    · cases h

theorem ObjCase.subst (σ : Subst) {ls : List String} {es : List Expr} {T P : Ty}
    (h : ObjCase ls es T P) : ObjCase ls es (T.subst σ) (P.subst σ) := by
  cases h with
  | self => exact .self
  | variant hw hl hi hP ht =>
    exact .variant (Ty.whnf_subst_of_app hw σ) hl hi (by simp [hP]) (Ty.tagOf_subst ht σ)

theorem HasTypeS.subst {S : Sys} (hS : S.Substable) (σ : Subst) (h : HasTypeS S L C Γ R rm md e τ) :
    HasTypeS S L (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) rm md e
      (τ.subst σ) := by
  induction h with
  | lit hl => cases hl <;> exact .lit (by constructor)
  | var hi hlen hc =>
    rw [Scheme.inst_subst]
    refine .var (by simp [List.getElem?_map, hi]) (by simpa [Scheme.subst] using hlen) ?_
    intro c hc'
    rw [← Scheme.instPreds_subst] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
    exact (hc c₀ hc₀).substS hS σ
  | func hlen _ ih =>
    refine .func (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def] using ih
  | @funcCheck T n C Γ θ τs ρ body R rm hT hT₀ hlen _ ih =>
    refine .funcCheck (Ty.whnf_subst_of_app hT σ) (hS.closed σ hT₀) (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def] using ih
  | app _ hlen _ ihf iha =>
    refine .app (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    refine .let_ (s.subst σ) (F ++ σ.map Prod.fst) (fun m hm => ?_) ?_ ?_ ?_ (by simpa using ih₂)
    · have hσ : ∀ p ∈ σ, p.1 < m := fun p hp => hm p.1 (by simp; exact .inr ⟨_, hp⟩)
      rw [← Scheme.open_subst s hσ, ← Scheme.openPreds_subst s hσ, ← List.map_append]
      exact ih₁ m (fun a ha => hm a (by simp [ha]))
    · simpa [Scheme.subst] using hv
    · exact hs.subst σ
    · intro a h
      obtain ⟨rfl, h'⟩ := ha a h
      rw [Scheme.subst_of_ftv_nil σ h'.2.2.1]
      exact ⟨rfl, h'⟩
  | letPoly a K h0 hp hf hr _ hv hw _ ih₁ ih₂ =>
    have ha : a.subst σ = a := Scheme.subst_of_ftv_nil σ hf
    refine .letPoly a K h0 hp hf hr (fun k hk => ?_) hv hw (by simpa [ha] using ih₂)
    have := ih₁ k hk
    rwa [Scheme.inst_subst, ha, rigids_subst] at this
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
    | plus hc => exact .binop (.plus (hc.substS hS σ)) ih₁ ih₂
    | minus => exact .binop .minus ih₁ ih₂
  | ret _ ih => exact .ret ih
  | throw_ _ ih => exact .throw_ ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | while_ _ _ ihc ihb => exact .while_ ihc ihb
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch _ _ ihb ihh => exact .tryCatch ihb (by simpa using ihh)
  | unwrap _ hs _ _ ih₁ ih₂ ih₃ =>
    exact .unwrap ih₁ (by simpa [Pred.subst] using hs.substS hS σ) ih₂ (by simpa using ih₃)
  | tryFinally _ _ ihb ihf => exact .tryFinally ihb ihf
  | @obj _ _ _ _ _ _ _ _ τs hes hks hτs hss hL _ hm ih =>
    simp only [Ty.subst_app, objSlots_subst]
    refine .obj (τs := τs.map (·.subst σ)) hes hks (by simpa using hτs) (by simpa using hss) hL (fun p hp => ?_) (fun x hx => ?_)
    · rw [List.zip_map_right] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
    · rw [zip4_map] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := (hm y hy).subst σ
      simpa [Ty.subst_app, objSlots_subst] using this
  | @cls _ _ _ τs _ _ _ _ _ hes hks hτs hss hnd hL _ hm ih =>
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
      have := (hm y hy).subst hS σ
      simpa [Ty.subst_app, objSlots_subst] using this
  | ctor hlen _ ih =>
    refine .ctor (by simpa using hlen) ?_
    simpa [List.map_append, Function.comp_def] using ih
  | new_ _ hlen _ hρ hss ihf iha =>
    refine .new_ (by simpa using ihf) (by simpa using hlen) (fun p hp => ?_) (by simpa using hρ.subst σ)
      (by simpa using hss)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | get _ hp ih => exact .get ih (by simpa [Pred.subst] using hp.substS hS σ)
  | set _ hp _ ihe ihv => exact .set ihe (by simpa [Pred.subst] using hp.substS hS σ) ihv
  | @spread _ _ _ _ _ _ _ ps ks τs _ hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    simp only [Ty.subst_app] at ih₁ ih₂ ⊢
    refine .spread (ps := ps.map (·.subst σ)) (ks := ks.map (·.subst σ)) (τs := τs.map (·.subst σ))
      (by simpa using hps) (by simpa using hks) (by simpa using hτs) (by simpa using hss)
      (by simpa using hrs) ih₁ ?_ (fun p hp => ?_)
    · simpa [slots3_subst] using ih₂
    · rw [← mergePreds_subst] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hm q hq).substS hS σ
  | arr _ ih => exact .arr ih
  | arrCheck hT hT₀ _ ih =>
    exact .arrCheck (Ty.whnf_subst_of_app hT σ) (hS.closed σ hT₀) (fun e he => by simpa using ih e he)
  | index _ _ hp ihe ihi => exact .index ihe ihi (by simpa [Pred.subst] using hp.substS hS σ)
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    exact .setIndex ihe ihi (by simpa [Pred.subst] using hp.substS hS σ)
      (by simpa [Pred.subst] using hw.substS hS σ) ihv
  | mcall _ hp hlen _ ihe iha =>
    refine .mcall ihe (by simpa [Pred.subst] using hp.substS hS σ) (by simpa using hlen)
      (fun p hp => ?_)
    rw [List.zip_map_right] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact iha q hq
  | conv _ he ih => exact .conv ih (he.subst σ)
  | inj _ hT hi ih =>
    exact .inj ih (hS.closed σ hT) (by rw [← hS.injPred σ _ hT]; exact hi.substS hS σ)
  | drop _ ih => exact .drop ih
  | litStr hw => exact .litStr (Ty.whnf_subst_of_app hw σ)
  | objCheck hc hn hk hl hL hd he _ ih =>
    refine .objCheck (hc.subst σ) hn hk hl hL (Ty.dataFields_subst σ hd) ?_ (fun p hp => ?_)
    · simpa [objSlots_subst, List.map_map, Function.comp_def] using he.subst σ
    · rw [List.zip_map_right] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih q hq
  | caseTag _ hc _ _ ih₁ ih₂ ih₃ =>
    exact .caseTag ih₁ (by simpa [Pred.subst] using hc.substS hS σ) (by simpa using ih₂)
      (by simpa using ih₃)

/-- The narrow system survives substitution. -/
theorem Sys.narrow_substable : Sys.narrow.Substable where
  inst σ := fun h => InstEq.subst σ h
  closed σ := fun {T} hT => by
    show (T.subst σ).ftv = []
    rw [Ty.closed_subst hT]; exact hT
  injPred σ τ := fun {T} hT => by
    show Pred.subst σ ⟨.inject T, [τ]⟩ = ⟨.inject (T.subst σ), [τ.subst σ]⟩
    simp [Pred.subst, Ty.closed_subst hT]

theorem HasTypeS.subst' (σ : Subst) (h : HasType L C Γ R rm md e τ) :
    HasType L (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) rm md e
      (τ.subst σ) := h.subst Sys.narrow_substable σ

end Inty
