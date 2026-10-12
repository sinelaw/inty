import Inty.Soundness

/-!
# Jones's rule for `let`, and how `HasType` relates to it

`HasType`'s `let` rule writes inty's generalisation as a side condition: a
binding's scheme has its constraints on its quantified variables
(`Scheme.Simple`). The textbook rule for qualified types (Jones, *Qualified
Types*, 1994; HM(X)'s without its satisfiability check) generalises over
any constraints: `e₁` is typed assuming the scheme's constraints, whatever
they are, and each use of the binding establishes them.

`Sys.jones` is the system inference implements with that rule
(`Sys.anyScheme`), and `HasTypeJ` its typing judgement. Then:

* every typing of `HasType` is one of `HasTypeJ` (`HasType.toJones`);
* `HasTypeJ` is sound, as `HasType` is (`jones_eval_sound`,
  `jones_never_stuck`): the side condition is not needed for soundness,
  only for inference to find every typing;
* the converse fails (`jones_separates`): Jones's rule types
  `const f = (y) => true + true; 1`, whose unused binding carries the
  constraint `Plus boolean`, which no type satisfies, and `HasType` doesn't,
  as inty doesn't. So `HasType` is the textbook system restricted to
  bindings whose schemes' constraints are on their quantified variables.

Nothing here changes `HasType`: `Sys.narrow.anyScheme` is `false`.
-/

namespace Inty

/-! ## Systems ordered by what they allow -/

/-- `S₂` allows whatever `S₁` does: more instances and expected types, the
same injections, and any scheme if `S₁` does. -/
structure Sys.Le (S₁ S₂ : Sys) : Prop where
  inst : ∀ {p : Pred}, S₁.inst p → S₂.inst p
  closed : ∀ {T : Ty}, S₁.closed T → S₂.closed T
  injPred : S₁.injPred = S₂.injPred
  anyScheme : S₁.anyScheme = true → S₂.anyScheme = true
  assignSub : S₁.assignSub = true → S₂.assignSub = true

theorem EntailsS.mono {S₁ S₂ : Sys} (hle : S₁.Le S₂) {C : List Pred} {p : Pred}
    (h : EntailsS S₁ C p) : EntailsS S₂ C p :=
  h.elim (fun hi => .inl (hle.inst hi)) .inr

theorem BinOpTyS.mono {S₁ S₂ : Sys} (hle : S₁.Le S₂) {C : List Pred} {op : BinOp} {τ₁ τ₂ τ : Ty}
    (h : BinOpTyS S₁ C op τ₁ τ₂ τ) : BinOpTyS S₂ C op τ₁ τ₂ τ := by
  cases h with
  | plus hp => exact .plus (hp.mono hle)
  | num h => exact .num h
  | strictEq => exact .strictEq

theorem MemberSlotS.mono {S₁ S₂ : Sys} (hle : S₁.Le S₂) {C : List Pred} {T : Ty} {k : ClassKind}
    {e : Expr} {τ s : Ty} (h : MemberSlotS S₁ C T k e τ s) : MemberSlotS S₂ C T k e τ s := by
  cases h with
  | data => exact .data
  | arrow hθ hn => exact .arrow hθ (hn.mono hle)
  | method hθ => exact .method hθ
  | getter hθ => exact .getter hθ

/-- A typing in a system is one in any system that allows more. -/
theorem HasTypeS.mono {S₁ S₂ : Sys} (hle : S₁.Le S₂) {L : List String} {C : List Pred} {Γ : Ctx}
    {R : Option Ty} {rm md : Mode} {e : Expr} {τ : Ty} (h : HasTypeS S₁ L C Γ R rm md e τ) :
    HasTypeS S₂ L C Γ R rm md e τ := by
  induction h with
  | lit hl => exact .lit hl
  | var hi hlen hc => exact .var hi hlen (fun c hc' => (hc c hc').mono hle)
  | func hlen _ ih => exact .func hlen ih
  | funcCheck hT hT₀ hlen _ ih => exact .funcCheck hT (hle.closed hT₀) hlen ih
  | app _ hlen _ ihf iha => exact .app ihf hlen iha
  | let_ s F _ hv hs ha _ ih₁ ih₂ => exact .let_ s F ih₁ hv (hs.imp hle.anyScheme id) ha ih₂
  | letPoly a K h0 hp hf hr _ hv hw _ ih₁ ih₂ => exact .letPoly a K h0 hp hf hr ih₁ hv hw ih₂
  | assign hi ha hp _ ih => exact .assign hi ha hp ih
  | assignCheck hs hi ha hp hT hc _ ih =>
    exact .assignCheck (hle.assignSub hs) hi ha hp hT (hle.closed hc) ih
  | cond _ _ _ ihc iht ihe => exact .cond ihc iht ihe
  | unop hop _ ih => exact .unop hop ih
  | binop hop _ _ ih₁ ih₂ => exact .binop (hop.mono hle) ih₁ ih₂
  | ret _ ih => exact .ret ih
  | throw_ _ ih => exact .throw_ ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | while_ _ _ ihc ihb => exact .while_ ihc ihb
  | break_ => exact .break_
  | continue_ => exact .continue_
  | tryCatch _ _ ihb ihh => exact .tryCatch ihb ihh
  | tryFinally _ _ ihb ihf => exact .tryFinally ihb ihf
  | obj hes hks hτs hss hL _ hm ih => exact .obj hes hks hτs hss hL ih hm
  | cls hes hks hτs hss hnd hL _ hm ih =>
    exact .cls hes hks hτs hss hnd hL ih (fun x hx => (hm x hx).mono hle)
  | ctor hlen _ ih => exact .ctor hlen ih
  | new_ _ hlen _ hρ hss ihf iha => exact .new_ ihf hlen iha hρ hss
  | get _ hp ih => exact .get ih (hp.mono hle)
  | set _ hp _ ihe ihv => exact .set ihe (hp.mono hle) ihv
  | spread hps hks hτs hss hrs _ _ hm ih₁ ih₂ =>
    exact .spread hps hks hτs hss hrs ih₁ ih₂ (fun p hp => (hm p hp).mono hle)
  | arr _ ih => exact .arr ih
  | arrCheck hT hT₀ _ ih => exact .arrCheck hT (hle.closed hT₀) ih
  | index _ _ hp ihe ihi => exact .index ihe ihi (hp.mono hle)
  | setIndex _ _ hp hw _ ihe ihi ihv => exact .setIndex ihe ihi (hp.mono hle) (hw.mono hle) ihv
  | mcall _ hp hlen _ ihe iha => exact .mcall ihe (hp.mono hle) hlen iha
  | unwrap _ hs _ _ ih₁ ih₂ ih₃ => exact .unwrap ih₁ (hs.mono hle) ih₂ ih₃
  | litStr hw => exact .litStr hw
  | objCheck hc hn hk hl hL hd he _ ih => exact .objCheck hc hn hk hl hL hd he ih
  | caseTag _ hc _ _ ih₁ ih₂ ih₃ => exact .caseTag ih₁ (hc.mono hle) ih₂ ih₃
  | conv _ he ih => exact .conv ih he
  | inj _ hT hi ih => exact .inj ih (hle.closed hT) (by rw [← hle.injPred]; exact hi.mono hle)
  | drop _ ih => exact .drop ih

/-! ## Jones's system -/

/-- The system inference implements, with Jones's `let` rule: a binding's
scheme may have any constraints. -/
def Sys.jones : Sys := { Sys.narrow with anyScheme := true }

/-- Typing with Jones's `let` rule. -/
abbrev HasTypeJ := HasTypeS Sys.jones

theorem Sys.jones_narrowLike : Sys.jones.NarrowLike := ⟨rfl, rfl⟩

theorem Sys.narrow_le_jones : Sys.narrow.Le Sys.jones := ⟨id, id, rfl, fun _ => rfl, id⟩

/-- Every typing of `HasType` is one with Jones's rule. -/
theorem HasType.toJones {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode}
    {e : Expr} {τ : Ty} (h : HasType L C Γ R rm md e τ) : HasTypeJ L C Γ R rm md e τ :=
  h.mono Sys.narrow_le_jones

/-- Soundness with Jones's rule: a typing runs out of clock, completes
abruptly, or returns a value of its type, as `eval_sound` says of
`HasType`. -/
theorem jones_eval_sound (clock : Nat) (ht : HasTypeJ L C Γ R rm md e τ) (hC : HoldsOrVar C)
    (hG : G W (Γ.map Scheme.toW) env) (hH : HeapOK clock W h) : Safe (run clock env h e) clock W τ R :=
  eval_soundW clock (ht.toWideOf Sys.jones_narrowLike) hC.toW hG hH

/-- A closed program typed with Jones's rule never gets stuck. -/
theorem jones_never_stuck (ht : HasTypeJ L C [] none rm md e τ) (hC : HoldsOrVar C) (clock : Nat)
    (s : Stuck) : eval clock [] [] e ≠ .stuck s :=
  never_stuckW (ht.toWideOf Sys.jones_narrowLike) hC.toW clock s

/-! ## The separating program -/

/-- `const f = (y) => true + true; 1`. -/
def jonesExample : Expr :=
  .let_ false none (.func 1 (.binop .plus (.lit (.boolean true)) (.lit (.boolean true))))
    (.lit (.number 1))

/-- `f`'s scheme with Jones's rule: `∀ θ y. Plus boolean ⇒ (y) => boolean`,
with `this` the type `θ`. -/
def jonesScheme : Scheme :=
  ⟨2, .fn (.bound 0) [.bound 1] .boolean, [⟨.plus, [.boolean]⟩]⟩

theorem jonesExample_typed : HasTypeJ L [] [] none .synth .synth jonesExample .number := by
  refine .let_ jonesScheme [] (fun m _ => ?_) (.inr ⟨.func, rfl⟩) (.inl rfl) (fun _ h => by cases h)
    (.lit .number)
  show HasTypeJ L ([] ++ jonesScheme.openPreds m) [] none .synth .synth
    (.func 1 (.binop .plus (.lit (.boolean true)) (.lit (.boolean true))))
    (.fn (.var m) [.var (m + 1)] (.app .boolean []))
  refine .func (τs := [.var (m + 1)]) rfl
    (.binop (.plus (.of_mem ?_)) (.lit (.boolean (b := true))) (.lit (.boolean (b := true))))
  simp [jonesScheme, Scheme.openPreds, Scheme.instPreds, PPred.inst, PTy.inst, varBlock]

theorem jonesExample_untyped : ¬ HasType L [] [] none .synth .synth jonesExample τ := by
  intro h
  obtain ⟨_, -, h⟩ := h.top_synth
  cases h with
  | let_ s F hgen _ hs _ _ =>
    have hs : s.Simple := hs.resolve_left (by simp [Sys.narrow])
    have h₁ := hgen (maxPlusOne F) (fun a ha => lt_maxPlusOne a ha)
    obtain ⟨_, -, h₁⟩ := h₁.top_synth
    cases h₁ with
    | func _ hb =>
      obtain ⟨_, -, hb⟩ := hb.top_synth
      cases hb with
      | binop hop hl _ =>
        cases hop with
        | num h => simp [BinOp.numeric] at h
        | plus hc =>
          obtain ⟨_, e₁, hl⟩ := hl.top_synth
          cases hl with
          | lit hl =>
            cases hl
            rcases hc with hi | ⟨q, hq, hpq⟩
            · -- `Plus` holds of numbers and strings only.
              obtain ⟨q, hq, hi⟩ := hi
              cases hi
              case plusNumber => exact absurd (e₁.trans (PredEq.one hq).2) (fun e => by cases TyEq.con e)
              case plusString => exact absurd (e₁.trans (PredEq.one hq).2) (fun e => by cases TyEq.con e)
              all_goals (obtain ⟨hcls, -, -⟩ := hq; cases hcls)
            · -- An assumption of the scheme is on one of its variables.
              simp only [List.nil_append, Scheme.openPreds, Scheme.instPreds, List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq
              rcases hs p hp with ⟨_, _, i, hi, rest, hargs⟩ | ⟨_, _, _, _, _, hmerge, _⟩
              · obtain ⟨_, hlen, hz⟩ := hpq
                simp only [PPred.inst, hargs, List.map_cons, List.zip_cons_cons, List.mem_cons,
                  forall_eq_or_imp] at hz
                have hv := hz.1
                have hvar : (PTy.bound i).inst (varBlock (maxPlusOne F) s.arity) =
                    .var (maxPlusOne F + i) := by
                  simp [PTy.inst, varBlock, hi]
                rw [hvar] at hv
                exact TyEq.var_app (e₁.trans hv).symm
              · obtain ⟨hcls, -, -⟩ := hpq
                simp only [PPred.inst, hmerge] at hcls
                cases hcls

/-- Jones's rule types more than `HasType`: a binding whose scheme's
constraint is on no variable of it, and holds of no type. -/
theorem jones_separates :
    HasTypeJ L [] [] none .synth .synth jonesExample .number ∧
      ∀ τ, ¬ HasType L [] [] none .synth .synth jonesExample τ :=
  ⟨jonesExample_typed, fun _ => jonesExample_untyped⟩

end Inty
