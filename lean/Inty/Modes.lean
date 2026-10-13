import Inty.InferComplete

/-!
# What checking mode adds

`HasType` checks an expression against an expected type (an annotation's)
in two ways. An expression that doesn't take the type in (`Expr.pushes`) is
synthesised and its type injected into the expected one (`HasTypeS.inj`),
or dropped into `unknown` (`HasTypeS.drop`), and nothing else:
`HasTypeS.inj_inv`. A literal form that takes it in (a function, an array,
an object literal, a string literal) has a rule of its own, which pushes
the type into its parts. Those rules are the ones inference implements
(`Expr.pushes`), and each types something synthesis and injection can't:
`/** const f: (Number) => Number | null */ const f = (x) => null` pushes
the result type into the body (`funcCheck_needed`), `[null]` as a
`(Number | null)[]` pushes the element type into the elements
(`arrCheck_needed`), and `"a"` has the type of the string `"a"` only when
checked against it (`litStr_needed`).
-/

namespace Inty

/-- Checking an expression that doesn't take the expected type in is
synthesis followed by injection, or dropping the value. -/
theorem check_of_not_pushes {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty}
    {rm : Mode} {e : Expr} {T : Ty} (h : HasType L C Γ R rm .check e T) (hp : e.pushes T = false) :
    ∃ τ₀, HasType L C Γ R rm .synth e τ₀ ∧ (T = .unknown ∨ Entails C ⟨.inject T, [τ₀]⟩) :=
  h.inj_inv hp

/-- Nothing injects into a type that isn't a sum, but itself and, into a
`String`, a string literal type. -/
theorem not_entails_inject {T τ : Ty} (hm : ∀ z σ, ¬ TyEq T (.maybe z σ))
    (hv : ∀ ts Rs, T.whnf ≠ .variant .typeOf ts Rs) (hne : ¬ TyEq τ T)
    (hl : ∀ s, ¬ TyEq τ (.strLit s)) : ¬ Entails [] ⟨.inject T, [τ]⟩ := by
  rintro (⟨q, hq, hi⟩ | ⟨c, hc, -⟩)
  · cases hi with
    | injectSelf _ =>
      obtain ⟨hcls, hτ⟩ := PredEq.one hq
      cases hcls
      exact hne hτ
    | injectNothing he _ =>
      obtain ⟨hcls, -⟩ := PredEq.one hq
      cases hcls
      exact hm _ _ he
    | injectSome he _ _ _ _ =>
      obtain ⟨hcls, -⟩ := PredEq.one hq
      cases hcls
      exact hm _ _ he
    | injectArm _ hw _ _ _ _ _ _ =>
      obtain ⟨hcls, -⟩ := PredEq.one hq
      cases hcls
      exact hv _ _ hw
    | injectLit _ _ =>
      obtain ⟨hcls, hτ⟩ := PredEq.one hq
      exact hl _ hτ
    | _ => obtain ⟨hcls, -, -⟩ := hq; cases hcls
  · cases hc

theorem not_tyEq_con {c c' : Con} {xs ys : List Ty} (h : c ≠ c') : ¬ TyEq (.app c xs) (.app c' ys) :=
  fun e => h (TyEq.con e)

/-! ## A string literal -/

theorem litStr_needed {L : List String} :
    HasType L [] [] none .synth .check (.lit (.string "a")) (.strLit "a") ∧
      ∀ τ, HasType L [] [] none .synth .synth (.lit (.string "a")) τ →
        ¬ TyEq τ (.strLit "a") ∧ ¬ Entails [] ⟨.inject (.strLit "a"), [τ]⟩ := by
  refine ⟨.litStr rfl, fun τ h => ?_⟩
  obtain ⟨τ₀, h₀, ht⟩ := h.top_synth
  cases ht with
  | lit hl =>
    cases hl
    have hne : ¬ TyEq τ (.strLit "a") := fun e => not_tyEq_con (by simp) (h₀.trans e)
    exact ⟨hne, not_entails_inject (fun _ _ e => not_tyEq_con (by simp) e)
      (fun _ _ h => by simp at h) hne
      (fun _ e => not_tyEq_con (by simp) (h₀.trans e))⟩

/-! ## An array literal -/

theorem arrCheck_needed {L : List String} :
    HasType L [] [] none .synth .check (.arr [.lit .null]) (.array (.nullable .number)) ∧
      ∀ τ, HasType L [] [] none .synth .synth (.arr [.lit .null]) τ →
        ¬ TyEq τ (.array (.nullable .number)) ∧
          ¬ Entails [] ⟨.inject (.array (.nullable .number)), [τ]⟩ := by
  refine ⟨.arrCheck rfl rfl fun e he => ?_, fun τ h => ?_⟩
  · simp only [List.mem_singleton] at he; subst he
    exact .inj (.lit .null) rfl (.inl (Inst.instEq (.injectNothing (TyEq.refl _) rfl)))
  · obtain ⟨τ₀, h₀, ht⟩ := h.top_synth
    cases ht with
    | arr hes =>
      obtain ⟨τ₁, h₁, ht₁⟩ := (hes (.lit .null) (by simp)).top_synth
      cases ht₁ with
      | lit hl =>
        cases hl
        have hne : ¬ TyEq τ (.array (.nullable .number)) := fun e => by
          obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp (h₀.trans e)
          exact not_tyEq_con (c := .null) (c' := .maybe .null) (by simp)
            (h₁.trans (hz (_, .nullable .number) List.mem_cons_self))
        exact ⟨hne, not_entails_inject (fun _ _ e => not_tyEq_con (by simp) e)
          (fun _ _ h => by simp at h) hne
      (fun _ e => not_tyEq_con (by simp) (h₀.trans e))⟩

/-! ## A function -/

theorem funcCheck_needed {L : List String} :
    HasType L [] [] none .synth .check (.func 1 (.lit .null)) (.fn .undefined [.number] (.nullable .number)) ∧
      ∀ τ, HasType L [] [] none .synth .synth (.func 1 (.lit .null)) τ →
        ¬ TyEq τ (.fn .undefined [.number] (.nullable .number)) ∧
          ¬ Entails [] ⟨.inject (.fn .undefined [.number] (.nullable .number)), [τ]⟩ := by
  refine ⟨.funcCheck rfl rfl rfl ?_, fun τ h => ?_⟩
  · exact .inj (.lit .null) rfl (.inl (Inst.instEq (.injectNothing (TyEq.refl _) rfl)))
  · obtain ⟨τ₀, h₀, ht⟩ := h.top_synth
    cases ht with
    | func _ hb =>
      obtain ⟨τ₁, h₁, ht₁⟩ := hb.top_synth
      cases ht₁ with
      | lit hl =>
        cases hl
        have hne : ¬ TyEq τ (.fn .undefined [.number] (.nullable .number)) := fun e => by
          obtain ⟨-, -, hz⟩ := TyEq.app_iff.mp (h₀.trans e)
          exact not_tyEq_con (c := .null) (c' := .maybe .null) (by simp)
            (h₁.trans (hz (_, .nullable .number) (List.mem_cons_of_mem _ List.mem_cons_self)))
        exact ⟨hne, not_entails_inject (fun _ _ e => not_tyEq_con (by simp) e)
          (fun _ _ h => by simp at h) hne
      (fun _ e => not_tyEq_con (by simp) (h₀.trans e))⟩

end Inty
