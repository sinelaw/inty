import Inty.InferComplete

/-!
# Principal constrained types

`inferIn_complete` relates types only: every type a program has is an
instance of inference's. A constrained type is a type and the constraints
it holds under, and inference's is principal among them: its pair `(τ, P)`
is a typing, and the typings of the program, under assumptions `C`, are
exactly the instances `(τ.subst φ)` whose constraints `C` entails
(`P.subst φ`), up to equal types (`inferInC_principal`).

Nothing here changes inference: `inferInC` is `inferIn` keeping the
constraints it leaves (`inferIn_eq_inferInC`).
-/

namespace Inty

/-! ## A typing under constraints that entail its assumptions -/

theorem EntailsS.cutS {S : Sys} {C D : List Pred} {p : Pred} (h : EntailsS S D p)
    (hD : ∀ d ∈ D, EntailsS S C d) : EntailsS S C p :=
  h.elim .inl (fun ⟨q, hq, hpq⟩ => (hD q hq).of_predEq hpq.symm)

theorem EntailsS.weakenS {S : Sys} {C D : List Pred} {p : Pred} (h : EntailsS S C p)
    (hCD : ∀ c ∈ C, c ∈ D) : EntailsS S D p :=
  h.elim .inl (fun ⟨q, hq, hpq⟩ => .inr ⟨q, hCD q hq, hpq⟩)

theorem MemberSlotS.cutC {S : Sys} {C D : List Pred} {T : Ty} {k : ClassKind} {e : Expr}
    {τ s : Ty} (h : MemberSlotS S D T k e τ s) (hD : ∀ d ∈ D, EntailsS S C d) :
    MemberSlotS S C T k e τ s := by
  cases h with
  | data => exact .data
  | arrow hθ hn => exact .arrow hθ (hn.cutS hD)
  | method hθ => exact .method hθ
  | getter hθ => exact .getter hθ

theorem BinOpTyS.cutC {S : Sys} {C D : List Pred} {op : BinOp} {τ₁ τ₂ τ : Ty}
    (h : BinOpTyS S D op τ₁ τ₂ τ) (hD : ∀ d ∈ D, EntailsS S C d) : BinOpTyS S C op τ₁ τ₂ τ := by
  cases h with
  | plus hp => exact .plus (hp.cutS hD)
  | num h => exact .num h
  | strictEq => exact .strictEq

/-- A typing under assumptions `D` is one under any `C` that entails each of
them (the cut rule). -/
theorem HasTypeS.cutC {S : Sys} {L : List String} {D : List Pred} {Γ : Ctx} {R : Option Ty}
    {rm md : Mode} {e : Expr} {τ : Ty} (h : HasTypeS S L D Γ R rm md e τ) :
    ∀ {C : List Pred}, (∀ d ∈ D, EntailsS S C d) → HasTypeS S L C Γ R rm md e τ := by
  induction h with
  | lit hl => intro C _; exact .lit hl
  | var hi hlen hc => intro C hD; exact .var hi hlen (fun c hc' => (hc c hc').cutS hD)
  | func hlen _ ih => intro C hD; exact .func hlen (ih hD)
  | funcCheck hT hT₀ hlen _ ih => intro C hD; exact .funcCheck hT hT₀ hlen (ih hD)
  | app _ hlen _ ihf iha => intro C hD; exact .app (ihf hD) hlen (fun p hp => iha p hp hD)
  | let_ s F _ hv hs ha _ ih₁ ih₂ =>
    intro C hD
    refine .let_ s F (fun m hm => ih₁ m hm (fun d hd => ?_)) hv hs ha (ih₂ hD)
    rcases List.mem_append.mp hd with hd | hd
    · exact (hD d hd).weakenS (fun c hc => List.mem_append_left _ hc)
    · exact .of_mem (List.mem_append_right _ hd)
  | letPoly a K h0 hp hf hr _ hv hw _ ih₁ ih₂ =>
    intro C hD
    exact .letPoly a K h0 hp hf hr (fun k hk => ih₁ k hk hD) hv hw (ih₂ hD)
  | assign hi ha hp _ ih => intro C hD; exact .assign hi ha hp (ih hD)
  | cond _ _ _ ihc iht ihe => intro C hD; exact .cond (ihc hD) (iht hD) (ihe hD)
  | unop hop _ ih => intro C hD; exact .unop hop (ih hD)
  | binop hop _ _ ih₁ ih₂ => intro C hD; exact .binop (hop.cutC hD) (ih₁ hD) (ih₂ hD)
  | ret _ ih => intro C hD; exact .ret (ih hD)
  | throw_ _ ih => intro C hD; exact .throw_ (ih hD)
  | seq _ _ ih₁ ih₂ => intro C hD; exact .seq (ih₁ hD) (ih₂ hD)
  | while_ _ _ ihc ihb => intro C hD; exact .while_ (ihc hD) (ihb hD)
  | break_ => intro C _; exact .break_
  | continue_ => intro C _; exact .continue_
  | tryCatch _ _ ihb ihh => intro C hD; exact .tryCatch (ihb hD) (ihh hD)
  | tryFinally _ _ ihb ihf => intro C hD; exact .tryFinally (ihb hD) (ihf hD)
  | obj hes hks hτs hss hL _ hm ih =>
    intro C hD; exact .obj hes hks hτs hss hL (fun p hp => ih p hp hD) hm
  | cls hes hks hτs hss hnd hL _ hm ih =>
    intro C hD
    exact .cls hes hks hτs hss hnd hL (fun i e k τ he hk hτ => ih i e k τ he hk hτ hD)
      (fun x hx => (hm x hx).cutC hD)
  | ctor hlen _ ih => intro C hD; exact .ctor hlen (ih hD)
  | new_ _ hlen _ hρ hss ihf iha =>
    intro C hD; exact .new_ (ihf hD) hlen (fun p hp => iha p hp hD) hρ hss
  | get _ hp ih => intro C hD; exact .get (ih hD) (hp.cutS hD)
  | set _ hp _ ihe ihv => intro C hD; exact .set (ihe hD) (hp.cutS hD) (ihv hD)
  | spread hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    intro C hD
    exact .spread hps hks hτs hss hrs (ih₁ hD) (ih₂ hD) (fun p hp => (hm p hp).cutS hD)
  | arr _ ih => intro C hD; exact .arr (fun e he => ih e he hD)
  | arrCheck hT hT₀ _ ih => intro C hD; exact .arrCheck hT hT₀ (fun e he => ih e he hD)
  | index _ _ hp ihe ihi => intro C hD; exact .index (ihe hD) (ihi hD) (hp.cutS hD)
  | setIndex _ _ hp hw _ ihe ihi ihv =>
    intro C hD; exact .setIndex (ihe hD) (ihi hD) (hp.cutS hD) (hw.cutS hD) (ihv hD)
  | mcall _ hp hlen _ ihe iha =>
    intro C hD; exact .mcall (ihe hD) (hp.cutS hD) hlen (fun p hp => iha p hp hD)
  | unwrap _ hs _ _ ih₁ ih₂ ih₃ =>
    intro C hD; exact .unwrap (ih₁ hD) (hs.cutS hD) (ih₂ hD) (ih₃ hD)
  | litStr hw => intro C _; exact .litStr hw
  | objCheck hc hn hk hl hL hd he _ ih =>
    intro C hD; exact .objCheck hc hn hk hl hL hd he (fun p hp => ih p hp hD)
  | caseTag _ hc _ _ ih₁ ih₂ ih₃ =>
    intro C hD; exact .caseTag (ih₁ hD) (hc.cutS hD) (ih₂ hD) (ih₃ hD)
  | conv _ he ih => intro C hD; exact .conv (ih hD) he
  | inj _ hT hi ih => intro C hD; exact .inj (ih hD) hT (hi.cutS hD)
  | drop _ ih => intro C hD; exact .drop (ih hD)

/-! ## Inference's constrained type -/

/-- What inference finds for `e`: its type and the constraints left, which
`inferIn` drops. -/
def inferInC (L : List String) (Γ : Ctx) (e : Expr) : Option (Ty × List Pred) :=
  if e.scoped (Γ.map fun _ => false) then
    match infer L Γ none .synth none e 0 with
    | none => none
    | some o =>
      match improveAll true o.preds.length o.preds with
      | none => none
      | some (σi, preds) => if preds.all Pred.settled then some (o.τ.subst σi, preds) else none
  else none

theorem inferIn_eq_inferInC (L : List String) (Γ : Ctx) (e : Expr) :
    inferIn L Γ e = (inferInC L Γ e).map Prod.fst := by
  unfold inferIn inferInC
  split
  · cases infer L Γ none .synth none e 0 with
    | none => rfl
    | some o =>
      simp only
      cases improveAll true o.preds.length o.preds with
      | none => rfl
      | some r =>
        obtain ⟨σi, preds⟩ := r
        simp only
        split <;> rfl
  · rfl

/-- Inference's constrained type is a typing: the program has its type
under its constraints, which hold or are on type variables. -/
theorem inferInC_sound {L : List String} {Γ : Ctx} {e : Expr} {τ : Ty} {P : List Pred}
    (hΓ : ctxFtv Γ = []) (h : inferInC L Γ e = some (τ, P)) :
    HoldsOrVar P ∧ HasType L P Γ none .synth .synth e τ := by
  simp only [inferInC] at h
  split at h
  rotate_left
  · cases h
  split at h
  · cases h
  rename_i o ho
  split at h
  · cases h
  rename_i σi preds himp
  split at h
  · rename_i hall
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hsat : Sat preds o.preds σi := by
      have := improveAll_sound _ himp (C := preds) (φ := []) (fun c hc => EntailsS.of_mem (by simpa using hc))
      intro c hc
      simpa [Pred.subst_compose] using this c hc
    have hclosed : ∀ σ : Subst, Ctx.subst σ Γ = Γ := fun σ =>
      ctx_subst_id (fun a ha => by simp [hΓ] at ha)
    exact ⟨HoldsOrVar.of_settled hall, by simpa [hclosed] using infer_sound ho RetOk.synth .none σi preds hsat⟩
  · cases h

/-- Every typing of a program (with only monomorphic annotations, under
assumptions on type variables) is an instance of inference's constrained
type: its type is one up to equal types, and its assumptions entail the
instance's constraints. -/
theorem inferInC_complete {L : List String} {Γ : Ctx} {e : Expr} {τ' : Ty} {C : List Pred}
    (hΓ : ctxFtv Γ = []) (hC : ∀ p ∈ C, p.OnVarShaped)
    (hm : e.scoped (Γ.map fun _ => false) = true) (hmono : e.monoAnn = true)
    (ht : HasType L C Γ none .synth .synth e τ') :
    ∃ τ P, inferInC L Γ e = some (τ, P) ∧ ∃ φ, TyEq (τ.subst φ) τ' ∧ Sat C P φ := by
  obtain ⟨o, h, φ, _, hτ, hsat⟩ := infer_complete L e hmono (n := 0) (ψ := []) (R := none)
    RetOk.synth nofun .none .none (fun a ha => by rw [hΓ] at ha; cases ha) (fun a ha => by simp [Ret.ftv] at ha)
    (fun p hp => (hC p hp).assumable false) (by rw [Ctx.subst_nil]; exact CtxEq.refl Γ) (RetEq.refl _) ht
  obtain ⟨σi, preds, himp, habs, hsat', hkeep, _⟩ :=
    improveAll_complete (fun p hp => (hC p hp).assumable true) o.preds.length (Nat.le_refl _)
      hsat
  have hall : preds.all Pred.settled = true := List.all_eq_true.mpr (fun p hp =>
    Pred.settled_of_keep hC (hkeep p hp) (hsat' p hp))
  exact ⟨o.τ.subst σi, preds, by simp [inferInC, hm, h, himp, hall], φ, (habs _).trans hτ, hsat'⟩

/-- Every instance of inference's constrained type is a typing: its type
under any assumptions that entail its constraints. -/
theorem inferInC_instance {L : List String} {Γ : Ctx} {e : Expr} {τ : Ty} {P : List Pred}
    (hΓ : ctxFtv Γ = []) (h : inferInC L Γ e = some (τ, P)) (φ : Subst) {C : List Pred}
    (hφ : Sat C P φ) : HasType L C Γ none .synth .synth e (τ.subst φ) := by
  have ht := ((inferInC_sound hΓ h).2.subst Sys.narrow_substable φ)
  have hclosed : Γ.map (Scheme.subst φ) = Γ := ctx_subst_id (fun a ha => by simp [hΓ] at ha)
  rw [hclosed] at ht
  refine ht.cutC (fun d hd => ?_)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  exact hφ p hp

/-- Inference's constrained type `(τ, P)` is principal: under assumptions
on type variables, a program with only monomorphic annotations has the
type `τ'` exactly when `τ'` is an instance `τ.subst φ` (up to equal types)
whose constraints `P.subst φ` the assumptions entail. -/
theorem inferInC_principal {L : List String} {Γ : Ctx} {e : Expr} {τ : Ty} {P C : List Pred}
    (hΓ : ctxFtv Γ = []) (hC : ∀ p ∈ C, p.OnVarShaped)
    (hm : e.scoped (Γ.map fun _ => false) = true) (hmono : e.monoAnn = true)
    (h : inferInC L Γ e = some (τ, P)) (τ' : Ty) :
    HasType L C Γ none .synth .synth e τ' ↔ ∃ φ, TyEq (τ.subst φ) τ' ∧ Sat C P φ := by
  constructor
  · intro ht
    obtain ⟨τ₀, P₀, h₀, hφ⟩ := inferInC_complete hΓ hC hm hmono ht
    rw [h] at h₀
    simp only [Option.some.injEq, Prod.mk.injEq] at h₀
    obtain ⟨rfl, rfl⟩ := h₀
    exact hφ
  · rintro ⟨φ, hτ, hsat⟩
    exact .conv (inferInC_instance hΓ h φ hsat) hτ

/-- For closed programs: `inferProgram`'s constrained type. -/
def inferProgramC (e : Expr) : Option (Ty × List Pred) := inferInC e.labels.eraseDups [] e

/-- A closed program with only monomorphic annotations has the type `τ'`,
assuming constraints on type variables `C`, exactly when `τ'` is an
instance of its inferred constrained type whose constraints `C` entails. -/
theorem inferProgramC_principal {e : Expr} {τ : Ty} {P C : List Pred}
    (hC : ∀ p ∈ C, p.OnVarShaped) (hm : e.scoped [] = true) (hmono : e.monoAnn = true)
    (h : inferProgramC e = some (τ, P)) (τ' : Ty) :
    HasType e.labels.eraseDups C [] none .synth .synth e τ' ↔
      ∃ φ, TyEq (τ.subst φ) τ' ∧ Sat C P φ :=
  inferInC_principal (Γ := []) rfl hC hm hmono h τ'

end Inty
