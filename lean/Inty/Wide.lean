import Inty.TypeSubst

/-!
# The wide system

Soundness is proved in a system wider than the one inference implements
(`Sys.narrow`). The narrow system decides an `Inject` or a `Strip` by the
heads of the types involved, so that inference stays principal: `Strip τ
σ` holds of a sum's value `σ`, or of `τ` itself when its head is neither a
sum nor nothing. Instantiating a rigid type variable can turn such a head
into a sum, which the narrow instances no longer cover; the wide ones do,
since they hold of every value whatever the heads: a value of `τ` is one of
`τ`, of `Nullable τ`, and so on. Its injections take the expected type as
an argument (`Cls.injectW`), so a substitution reaches it, and it checks
against any expected type.

A narrow derivation is a wide one (`HasTypeS.toWide`), its constraints
translated (`Pred.toW`).
-/

namespace Inty

/-- The wide system's instances: the narrow ones but its injections, and
the injections and strippings that hold of every value whatever the
heads. -/
inductive InstW : Pred → Prop where
  | narrow : Inst p → (∀ T, p.cls ≠ .inject T) → InstW p
  | injectSelf : InstW ⟨.injectW, [T, T]⟩
  | injectNothing : InstW ⟨.injectW, [z.ty, .maybe z σ]⟩
  | injectSome : InstW ⟨.injectW, [σ, .maybe z σ]⟩
  | injectArm : Rs[(i : Nat)]? = some R → R.whnf = .app c xs → c.typeTag = some t →
      ts[i]? = some t → InstW ⟨.injectW, [R, .variant .typeOf ts Rs]⟩
  | stripSelf : InstW ⟨.strip, [τ, τ]⟩

theorem InstW.subst (σ : Subst) {p : Pred} (h : InstW p) : InstW (p.subst σ) := by
  cases h with
  | narrow h hc => exact .narrow (h.subst σ) hc
  | injectSelf => exact .injectSelf
  | injectNothing => simpa [Pred.subst, Nothing.ty, Ty.subst_app] using InstW.injectNothing
  | injectSome => simpa [Pred.subst, Ty.subst_app] using InstW.injectSome
  | @injectArm Rs i R c xs t ts hR hw hc hi =>
    simpa [Pred.subst, Ty.subst_app] using
      InstW.injectArm (Rs := Rs.map (·.subst σ)) (by simp [hR]) (Ty.whnf_subst_of_app hw σ) hc hi
  | stripSelf => exact .stripSelf

/-- A wide instance up to equal types. -/
def InstEqW (p : Pred) : Prop := ∃ q, PredEq p q ∧ InstW q

theorem InstEqW.subst (σ : Subst) {p : Pred} (h : InstEqW p) : InstEqW (p.subst σ) := by
  obtain ⟨q, hpq, hq⟩ := h
  exact ⟨q.subst σ, hpq.subst σ, hq.subst σ⟩

theorem InstEqW.of_predEq {p q : Pred} (h : PredEq p q) (hq : InstEqW q) : InstEqW p := by
  obtain ⟨r, hqr, hr⟩ := hq
  exact ⟨r, h.trans hqr, hr⟩

/-- The wide system: its instances, any expected type, and injections that
a substitution reaches. -/
def Sys.wide : Sys :=
  ⟨InstEqW, fun _ => True, fun h hq => InstEqW.of_predEq h hq, fun τ T => ⟨.injectW, [τ, T]⟩,
    fun h => PredEq.of_pairs (by simp) (zip_tyEq_cons h (zip_tyEq_cons (TyEq.refl _) zip_tyEq_nil))⟩

theorem Sys.wide_substable : Sys.wide.Substable where
  inst σ := fun h => InstEqW.subst σ h
  closed _ := fun _ => trivial
  injPred _ _ := fun _ => rfl

/-- Constraints each a wide instance or on a type variable. -/
abbrev HoldsOrVarW (C : List Pred) : Prop := HoldsOrVarS Sys.wide C

/-- A wide instance of a class whose instances are all narrow ones. -/
theorem InstEqW.narrow_of {p : Pred} (h : InstEqW p) (hi : p.cls ≠ .injectW)
    (hs : p.cls ≠ .strip) : InstEq p := by
  obtain ⟨q, hpq, hq⟩ := h
  cases hq with
  | narrow hq _ => exact ⟨_, hpq, hq⟩
  | injectSelf | injectNothing | injectSome => exact absurd hpq.1 hi
  | injectArm _ _ _ _ => exact absurd hpq.1 hi
  | stripSelf => exact absurd hpq.1 hs

/-- `EntailsS.instOrVar` for a class whose wide instances are narrow ones. -/
theorem EntailsS.instOrVarN {C : List Pred} {p : Pred} (hC : HoldsOrVarW C)
    (h : EntailsS Sys.wide C p) (hc : p.cls ≠ .merge) (hi : p.cls ≠ .injectW)
    (hs : p.cls ≠ .strip) : InstEq p ∨ ∃ t a rest, p.args = t :: rest ∧ t.whnf = .var a :=
  (h.instOrVar hC hc).imp (fun h => h.narrow_of hi hs) id

/-- `EntailsS.holdsOrVar` for a class whose wide instances are narrow ones. -/
theorem EntailsS.holdsOrVarN {C : List Pred} {p : Pred} (hC : HoldsOrVarW C)
    (h : EntailsS Sys.wide C p) (hi : p.cls ≠ .injectW) (hs : p.cls ≠ .strip) :
    InstEq p ∨ p.OnVar :=
  (h.holdsOrVar hC).imp (fun h => h.narrow_of hi hs) id

/-! ## From the narrow system -/

/-- A narrow constraint as a wide one: an injection takes the expected type
as an argument. -/
def Pred.toW : Pred → Pred
  | ⟨.inject T, [τ]⟩ => ⟨.injectW, [τ, T]⟩
  | p => p

def PPred.toW : PPred → PPred
  | ⟨.inject T, [π]⟩ => ⟨.injectW, [π, T.toPTy]⟩
  | p => p

def Scheme.toW (s : Scheme) : Scheme := ⟨s.arity, s.body, s.preds.map PPred.toW⟩

theorem Pred.toW_of_cls {p : Pred} (h : ∀ T, p.cls ≠ .inject T) : p.toW = p := by
  obtain ⟨c, args⟩ := p
  unfold Pred.toW
  split
  · rename_i T τ heq
    simp only [Pred.mk.injEq] at heq
    exact absurd heq.1 (h T)
  · rfl

theorem PPred.toW_inst (τs : List Ty) (p : PPred) : (p.toW).inst τs = (p.inst τs).toW := by
  obtain ⟨c, args⟩ := p
  unfold PPred.toW
  split
  · rename_i T π heq
    simp only [PPred.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [PPred.inst, Pred.toW]
  · rename_i hne
    by_cases hc : ∃ T, c = .inject T
    · obtain ⟨T, rfl⟩ := hc
      match args, hne with
      | [], _ => simp [PPred.inst, Pred.toW]
      | [π], hne => exact absurd rfl (hne T π)
      | _ :: _ :: _, _ => simp [PPred.inst, Pred.toW]
    · simp only [not_exists] at hc
      rw [Pred.toW_of_cls (by simpa [PPred.inst] using hc)]

@[simp] theorem Scheme.toW_arity (s : Scheme) : s.toW.arity = s.arity := rfl

@[simp] theorem Scheme.toW_inst (s : Scheme) (τs : List Ty) : s.toW.inst τs = s.inst τs := rfl

theorem Scheme.toW_instPreds (s : Scheme) (τs : List Ty) :
    s.toW.instPreds τs = (s.instPreds τs).map Pred.toW := by
  simp only [Scheme.instPreds, Scheme.toW, List.map_map]
  exact List.map_congr_left fun p _ => PPred.toW_inst τs p

@[simp] theorem Scheme.toW_mono (τ : Ty) : (Scheme.mono τ).toW = .mono τ := rfl

theorem Scheme.toW_of_preds_nil {s : Scheme} (h : s.preds = []) : s.toW = s := by
  obtain ⟨a, b, ps⟩ := s
  simp only at h; subst h; rfl

theorem PredEq.toW {p q : Pred} (h : PredEq p q) : PredEq p.toW q.toW := by
  obtain ⟨c, xs⟩ := p
  obtain ⟨c', ys⟩ := q
  obtain ⟨hc, hl, hz⟩ := h
  simp only at hc hl hz
  subst hc
  by_cases hT : ∃ T, c = .inject T
  · obtain ⟨T, rfl⟩ := hT
    match xs, ys, hl, hz with
    | [], [], _, _ => exact PredEq.refl _
    | [x], [y], _, hz =>
      simp only [Pred.toW]
      exact PredEq.of_pairs (by simp)
        (zip_tyEq_cons (hz (x, y) (by simp)) (zip_tyEq_cons (TyEq.refl _) zip_tyEq_nil))
    | x :: x' :: xs, y :: y' :: ys, hl, hz =>
      exact ⟨rfl, hl, hz⟩
  · simp only [not_exists] at hT
    rw [Pred.toW_of_cls (by simpa using hT), Pred.toW_of_cls (by simpa using hT)]
    exact ⟨rfl, hl, hz⟩

theorem Inst.toW {p : Pred} (h : Inst p) : InstEqW p.toW := by
  cases h with
  | injectSelf _ => exact ⟨_, PredEq.refl _, .injectSelf⟩
  | @injectNothing T z σ he _ =>
    exact ⟨⟨.injectW, [z.ty, .maybe z σ]⟩,
      PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons he zip_tyEq_nil)),
      .injectNothing⟩
  | @injectSome T z c args he _ _ _ _ =>
    exact ⟨⟨.injectW, [.app c args, .maybe z (.app c args)]⟩,
      PredEq.of_pairs (by simp) (zip_tyEq_cons (TyEq.refl _) (zip_tyEq_cons he zip_tyEq_nil)),
      .injectSome⟩
  | injectArm _ hw _ htag hi hR he _ =>
    obtain ⟨ys, hys, -⟩ := TyEq.whnf_app he (Ty.whnf_app _ _)
    exact ⟨_,
      PredEq.of_pairs (by simp) (zip_tyEq_cons he (zip_tyEq_cons (TyEq.of_whnf hw) zip_tyEq_nil)),
      .injectArm hR hys htag hi⟩
  | _ => exact ⟨_, PredEq.refl _, .narrow (by constructor <;> assumption) (by simp [Pred.toW])⟩

theorem InstEq.toW {p : Pred} (h : InstEq p) : InstEqW p.toW := by
  obtain ⟨q, hpq, hq⟩ := h
  exact InstEqW.of_predEq hpq.toW hq.toW

theorem EntailsS.toW {C : List Pred} {p : Pred} (h : Entails C p) :
    EntailsS Sys.wide (C.map Pred.toW) p.toW :=
  h.elim (fun h => .inl h.toW)
    (fun ⟨q, hq, hpq⟩ => .inr ⟨q.toW, List.mem_map_of_mem hq, hpq.toW⟩)

theorem Pred.OnVar.toW {p : Pred} (h : p.OnVar) : p.toW.OnVar := by
  by_cases hT : ∃ T, p.cls = .inject T
  · obtain ⟨T, hc⟩ := hT
    obtain ⟨c, args⟩ := p
    simp only at hc; subst hc
    rcases h with ⟨t, a, rest, he, hw⟩ | hm
    · simp only at he; subst he
      match rest with
      | [] => exact .inl ⟨t, a, [T], by simp [Pred.toW], hw⟩
      | x :: xs => exact .inl ⟨t, a, x :: xs, rfl, hw⟩
    · exact absurd hm (by simp [Pred.MergeOnVar])
  · simp only [not_exists] at hT
    rw [Pred.toW_of_cls hT]; exact h

theorem HoldsOrVar.toW {C : List Pred} (h : HoldsOrVar C) : HoldsOrVarW (C.map Pred.toW) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (h q hq).imp InstEq.toW Pred.OnVar.toW

theorem Pred.toW_plus {τ : Ty} : (⟨.plus, [τ]⟩ : Pred).toW = ⟨.plus, [τ]⟩ := rfl

theorem Scheme.toW_open (s : Scheme) (m : Nat) : s.toW.open m = s.open m := rfl

theorem Scheme.toW_openPreds (s : Scheme) (m : Nat) :
    s.toW.openPreds m = (s.openPreds m).map Pred.toW := s.toW_instPreds _

theorem PPred.toW_cls_args {p : PPred} :
    (∃ T π, p = ⟨.inject T, [π]⟩ ∧ p.toW = ⟨.injectW, [π, T.toPTy]⟩) ∨ p.toW = p := by
  obtain ⟨c, args⟩ := p
  unfold PPred.toW
  split
  · rename_i T π heq
    exact .inl ⟨T, π, heq, rfl⟩
  · exact .inr rfl

theorem Scheme.Simple.toW {s : Scheme} (h : s.Simple) : s.toW.Simple := by
  intro p hp
  simp only [Scheme.toW, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rcases PPred.toW_cls_args (p := q) with ⟨T, π, rfl, he⟩ | he
  · rw [he]
    rcases h _ hq with ⟨-, -, i, hi, rest, hr⟩ | ⟨_, _, _, _, _, h', -⟩
    · simp only at hr
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hr
      exact .inl ⟨by simp, by simp [Cls.arity], i, hi, [T.toPTy], rfl⟩
    · cases h'
  · rw [he]; exact h q hq

theorem memberCtx_toW (Γ : Ctx) (ks : List ClassKind) (τs : List Ty) (i : Nat) (k : ClassKind) :
    (memberCtx Γ ks τs i k).map Scheme.toW = memberCtx (Γ.map Scheme.toW) ks τs i k := by
  cases k <;> simp [memberCtx, List.map_append, List.map_map, Function.comp_def]

theorem BinOpTyS.toW {C : List Pred} (h : BinOpTy C op τ₁ τ₂ τ) :
    BinOpTyS Sys.wide (C.map Pred.toW) op τ₁ τ₂ τ := by
  cases h with
  | plus hc => exact .plus (by simpa [Pred.toW] using hc.toW)
  | minus => exact .minus

theorem MemberSlotS.toW {C : List Pred} (h : MemberSlot C T k e τ s) :
    MemberSlotS Sys.wide (C.map Pred.toW) T k e τ s := by
  cases h with
  | data => exact .data
  | arrow he hn => exact .arrow he (by simpa [Pred.toW] using hn.toW)
  | method he => exact .method he
  | getter he => exact .getter he

theorem mergePreds_toW : ∀ {ps ks τs ss rs : List Ty} {p : Pred},
    p ∈ mergePreds ps ks τs ss rs → p.toW = p
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, p, hp => by
    simp only [mergePreds, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact mergePreds_toW hp
  | [], _, _, _, _, _, hp | _ :: _, [], _, _, _, _, hp | _ :: _, _ :: _, [], _, _, _, hp
  | _ :: _, _ :: _, _ :: _, [], _, _, hp | _ :: _, _ :: _, _ :: _, _ :: _, [], _, hp => by
    simp [mergePreds] at hp

/-- A narrow derivation is a wide one, its constraints translated. -/
theorem HasTypeS.toWide {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode}
    {e : Expr} {τ : Ty} (h : HasType L C Γ R rm md e τ) :
    HasTypeS Sys.wide L (C.map Pred.toW) (Γ.map Scheme.toW) R rm md e τ := by
  induction h with
  | lit hl => exact .lit hl
  | var hi hlen hc =>
    rw [← Scheme.toW_inst]
    refine .var (by simp [List.getElem?_map, hi]) (by simpa using hlen) (fun c hc' => ?_)
    rw [Scheme.toW_instPreds] at hc'
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
    exact (hc c₀ hc₀).toW
  | func hlen _ ih =>
    exact .func hlen (by simpa [List.map_append, Function.comp_def] using ih)
  | funcCheck hT _ hlen _ ih =>
    exact .funcCheck hT trivial hlen (by simpa [List.map_append, Function.comp_def] using ih)
  | app _ hlen _ ihf iha => exact .app ihf hlen iha
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    refine .let_ s.toW F (fun m hm => ?_) (by simpa [Scheme.toW] using hv) hs.toW ?_
      (by simpa using ih₂)
    · have := ih₁ m hm
      rwa [List.map_append, ← Scheme.toW_openPreds] at this
    · intro a h
      obtain ⟨rfl, h'⟩ := ha a h
      rw [Scheme.toW_of_preds_nil h'.2.1]
      exact ⟨rfl, h'⟩
  | letPoly a K h0 hp hf hr _ hv hw _ ih₁ ih₂ =>
    exact .letPoly a K h0 hp hf hr ih₁ hv hw (by simpa [Scheme.toW_of_preds_nil hp] using ih₂)
  | assign hi ha hp _ ih =>
    rw [← Scheme.toW_inst]
    exact .assign (by simp [List.getElem?_map, hi]) (by simpa using ha)
      (by simp [Scheme.toW, hp]) (by simpa using ih)
  | cond _ _ _ ihc iht ihe => exact .cond ihc iht ihe
  | unop hop _ ih => exact .unop hop ih
  | binop hop _ _ ih₁ ih₂ => exact .binop hop.toW ih₁ ih₂
  | ret _ ih => exact .ret ih
  | throw_ _ ih => exact .throw_ ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | while_ _ _ ihc ihb => exact .while_ ihc ihb
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch _ _ ihb ihh => exact .tryCatch ihb (by simpa using ihh)
  | unwrap _ hs _ _ ih₁ ih₂ ih₃ => exact .unwrap ih₁ (by simpa [Pred.toW] using hs.toW) ih₂ (by simpa using ih₃)
  | tryFinally _ _ ihb ihf => exact .tryFinally ihb ihf
  | obj hes hks hτs hss hL _ hm ih => exact .obj hes hks hτs hss hL ih hm
  | cls hes hks hτs hss hnd hL _ hm ih =>
    refine .cls hes hks hτs hss hnd hL (fun i e k τ he hk hτ => ?_) (fun x hx => (hm x hx).toW)
    have := ih i e k τ he hk hτ
    rwa [memberCtx_toW] at this
  | ctor hlen _ ih => exact .ctor hlen (by simpa [List.map_append, Function.comp_def] using ih)
  | new_ _ hlen _ hρ hss ihf iha => exact .new_ ihf hlen iha hρ hss
  | get _ hp ih => exact .get ih (by simpa [Pred.toW] using hp.toW)
  | set _ hp _ ihe ihv => exact .set ihe (by simpa [Pred.toW] using hp.toW) ihv
  | spread hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    exact .spread hps hks hτs hss hrs ih₁ ih₂ (fun p hp => by
      simpa [mergePreds_toW hp] using (hm p hp).toW)
  | arr _ ih => exact .arr ih
  | arrCheck hT _ _ ih => exact .arrCheck hT trivial ih
  | index _ _ hp ihe ihi => exact .index ihe ihi (by simpa [Pred.toW] using hp.toW)
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    exact .setIndex ihe ihi (by simpa [Pred.toW] using hp.toW) (by simpa [Pred.toW] using hw.toW) ihv
  | mcall _ hp hlen _ ihe iha => exact .mcall ihe (by simpa [Pred.toW] using hp.toW) hlen iha
  | conv _ he ih => exact .conv ih he
  | inj _ _ hi ih => exact .inj ih trivial hi.toW
  | drop _ ih => exact .drop ih
  | litStr hw => exact .litStr hw
  | objCheck hc hn hk hl hL hd he _ ih => exact .objCheck hc hn hk hl hL hd he ih
  | caseTag _ hc _ _ ih₁ ih₂ ih₃ =>
    exact .caseTag ih₁ (by simpa [Pred.toW] using hc.toW) (by simpa using ih₂) (by simpa using ih₃)

end Inty
