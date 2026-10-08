import Inty.InferSound

/-!
# Pinned statements

The theorems' proofs are checked by Lean, but a theorem can be weakened
without anyone noticing: a hypothesis added, a conclusion dropped. Each
`example` here restates a headline theorem in full, so changing its
statement breaks the build until the statement here is changed too, in the
same diff, where a reviewer sees it.

The rejected programs pin the other direction: the typing rules must not
quietly become too permissive.
-/

namespace Inty.Statements

open Inty

/-! ## Headline theorems -/

example : ∀ (fuel : Nat) {C : List Ty} {Γ : Ctx} {env : Env} {e : Expr} {τ : Ty},
    HasType C Γ e τ → Holds C → EnvTy env Γ →
      eval fuel env e = .timeout ∨ ∃ v, eval fuel env e = .ok v ∧ ValTy v τ :=
  eval_sound

example : ∀ {e : Expr} {τ : Ty}, HasType [] [] e τ →
    ∀ (fuel : Nat) (s : Stuck), eval fuel [] e ≠ .stuck s :=
  never_stuck

example : ∀ {C : List Ty} {Γ : Ctx} {e : Expr} {τ : Ty} (σ : Subst), HasType C Γ e τ →
    HasType (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) e (τ.subst σ) :=
  fun σ h => h.subst σ

example : ∀ {fuel : Nat} {τ₁ τ₂ : Ty} {σ : Subst}, unify fuel τ₁ τ₂ = some σ →
    τ₁.subst σ = τ₂.subst σ :=
  unify_sound

example : ∀ {e : Expr} {Γ : Ctx} {n : Nat} {o : Out}, infer Γ e n = some o →
    ∀ φ C, (∀ c ∈ o.plus, Entails C (c.subst φ)) →
      HasType C (Ctx.subst φ (Ctx.subst o.σ Γ)) e (o.τ.subst φ) :=
  infer_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ → HasType [] [] e τ :=
  inferProgram_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ →
    ∀ (fuel : Nat) (s : Stuck), eval fuel [] e ≠ .stuck s :=
  inferProgram_never_stuck

/-! ## Programs the typing rules reject -/

private def num (n : Float) : Expr := .lit (.number n)
private def str (s : String) : Expr := .lit (.string s)

/-- An unbound variable. -/
example : ¬ HasType [] [] (.var 0) τ := by
  intro h; cases h with | var hi _ _ => simp at hi

/-- `1 + "a"`: `+` never mixes a `Number` with a `String`. -/
example : ¬ HasType [] [] (.binop .plus (num 1) (str "a")) τ := by
  intro h
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ => cases h₁ with | lit hl => cases hl; cases h₂ with | lit hl => cases hl

/-- `true + true`: `Boolean` is not a `Plus` instance, and nothing assumes it. -/
example : ¬ HasType [] [] (.binop .plus (.lit (.boolean true)) (.lit (.boolean true))) τ := by
  intro h
  cases h with
  | binop hop h₁ _ =>
    cases hop with
    | plus hc =>
      cases h₁ with
      | lit hl => cases hl; rcases hc with hc | hc <;> cases hc

/-- `"a" - 1`: `-` is `Number` only. -/
example : ¬ HasType [] [] (.binop .minus (str "a") (num 1)) τ := by
  intro h
  cases h with
  | binop hop h₁ _ => cases hop; cases h₁ with | lit hl => cases hl

/-- `-"a"`: unary `-` is `Number` only. -/
example : ¬ HasType [] [] (.unop .neg (str "a")) τ := by
  intro h
  cases h with
  | unop hop h₁ => cases hop; cases h₁ with | lit hl => cases hl

/-- `1(2)`: a number is not a function. -/
example : ¬ HasType [] [] (.app (num 1) (num 2)) τ := by
  intro h
  cases h with
  | app hf _ => cases hf with | lit hl => cases hl

end Inty.Statements
