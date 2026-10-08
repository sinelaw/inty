import Inty.InferSound
import Inty.Fuel

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

example : ∀ (fuel : Nat) {C : List Ty} {Γ : Ctx} {R : Option Ty} {env : Env} {e : Expr}
    {τ : Ty}, HasType C Γ R e τ → Holds C → EnvTy env Γ →
      eval fuel env e = .timeout ∨ (∃ v, eval fuel env e = .ok v ∧ ValTy v τ) ∨
        (∃ v, eval fuel env e = .thrown v) ∨
        (∃ τr v, R = some τr ∧ eval fuel env e = .returned v ∧ ValTy v τr) :=
  eval_sound

example : ∀ {e : Expr} {τ : Ty}, HasType [] [] none e τ →
    ∀ (fuel : Nat) (s : Stuck), eval fuel [] e ≠ .stuck s :=
  never_stuck

example : ∀ {C : List Ty} {Γ : Ctx} {R : Option Ty} {e : Expr} {τ : Ty} (σ : Subst),
    HasType C Γ R e τ →
      HasType (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) e (τ.subst σ) :=
  fun σ h => h.subst σ

example : ∀ {fuel : Nat} {τ₁ τ₂ : Ty} {σ : Subst}, unify fuel τ₁ τ₂ = some σ →
    τ₁.subst σ = τ₂.subst σ :=
  unify_sound

example : ∀ {e : Expr} {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out},
    infer Γ R e n = some o → ∀ φ C, (∀ c ∈ o.plus, Entails C (c.subst φ)) →
      HasType C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) e
        (o.τ.subst φ) :=
  infer_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ → HasType [] [] none e τ :=
  inferProgram_sound

example : ∀ {e : Expr} {τ : Ty}, inferProgram e = some τ →
    ∀ (fuel : Nat) (s : Stuck), eval fuel [] e ≠ .stuck s :=
  inferProgram_never_stuck

example : ∀ (n : Nat) {env : Env} {e : Expr} (k : Nat), eval n env e ≠ .timeout →
    eval (n + k) env e = eval n env e :=
  eval_mono

/-! ## Programs the typing rules reject -/

private def num (n : Float) : Expr := .lit (.number n)
private def str (s : String) : Expr := .lit (.string s)

/-- An unbound variable. -/
example : ¬ HasType [] [] none (.var 0) τ := by
  intro h; cases h with | var hi _ _ => simp at hi

/-- `1 + "a"`: `+` never mixes a `Number` with a `String`. -/
example : ¬ HasType [] [] none (.binop .plus (num 1) (str "a")) τ := by
  intro h
  cases h with
  | binop hop h₁ h₂ =>
    cases hop with
    | plus _ => cases h₁ with | lit hl => cases hl; cases h₂ with | lit hl => cases hl

/-- `true + true`: `Boolean` is not a `Plus` instance, and nothing assumes it. -/
example : ¬ HasType [] [] none (.binop .plus (.lit (.boolean true)) (.lit (.boolean true))) τ := by
  intro h
  cases h with
  | binop hop h₁ _ =>
    cases hop with
    | plus hc =>
      cases h₁ with
      | lit hl => cases hl; rcases hc with hc | hc <;> cases hc

/-- `"a" - 1`: `-` is `Number` only. -/
example : ¬ HasType [] [] none (.binop .minus (str "a") (num 1)) τ := by
  intro h
  cases h with
  | binop hop h₁ _ => cases hop; cases h₁ with | lit hl => cases hl

/-- `-"a"`: unary `-` is `Number` only. -/
example : ¬ HasType [] [] none (.unop .neg (str "a")) τ := by
  intro h
  cases h with
  | unop hop h₁ => cases hop; cases h₁ with | lit hl => cases hl

/-- `1(2)`: a number is not a function. -/
example : ¬ HasType [] [] none (.app (num 1) (num 2)) τ := by
  intro h
  cases h with
  | app hf _ => cases hf with | lit hl => cases hl

end Inty.Statements
