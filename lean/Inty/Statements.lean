import Inty.Builtins

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

example : ∀ (clock : Nat) {C : List Ty} {Γ : Ctx} {R : Option Ty} {env : Env} {e : Expr}
    {τ : Ty}, HasType C Γ R e τ → Holds C → G clock Γ env →
      (run clock env e).2 ≤ clock ∧
      ((run clock env e).1 = .timeout ∨
        (∃ v, (run clock env e).1 = .ok v ∧ V (run clock env e).2 τ v) ∨
        (∃ v, (run clock env e).1 = .thrown v) ∨
        (∃ v, (run clock env e).1 = .returned v ∧
          ∃ τr, R = some τr ∧ V (run clock env e).2 τr v)) :=
  fun clock _ _ _ _ _ _ h hC henv => eval_sound clock h hC henv

example : ∀ {e : Expr} {τ : Ty}, HasType [] [] none e τ →
    ∀ (clock : Nat) (s : Stuck), eval clock [] e ≠ .stuck s :=
  never_stuck

example : ∀ {e : Expr} {τ : Ty}, HasType [] builtinCtx none e τ →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv e ≠ .stuck s :=
  never_stuck_with_builtins

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
    ∀ (clock : Nat) (s : Stuck), eval clock [] e ≠ .stuck s :=
  inferProgram_never_stuck

example : ∀ {e : Expr} {τ : Ty}, inferIn builtinCtx e = some τ →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv e ≠ .stuck s :=
  inferIn_builtins_never_stuck

example : ∀ (c : Nat) (env : Env) (e : Expr), (run c env e).2 ≤ c :=
  run_clock_le

example : ∀ (c : Nat) (env : Env) (e : Expr) (k : Nat), (run c env e).1 ≠ .timeout →
    run (c + k) env e = ((run c env e).1, (run c env e).2 + k) :=
  run_mono

example : ∀ (n : Nat) {env : Env} {e : Expr} (k : Nat), eval n env e ≠ .timeout →
    eval (n + k) env e = eval n env e :=
  eval_mono

/-! ## The value relation

`eval_sound` is only as strong as `V`: a `V` that holds of everything would
make it trivial. So its clauses are pinned too. -/

example : V k .number v ↔ ∃ n, v = .number n := Iff.rfl
example : V k .string v ↔ ∃ s, v = .string s := Iff.rfl
example : V k .boolean v ↔ ∃ b, v = .boolean b := Iff.rfl
example : V k .undefined v ↔ v = .undefined := Iff.rfl
example : V k .null v ↔ v = .null := Iff.rfl
example : V k (.var a) v ↔ False := Iff.rfl
example : V k (.arrow τ₁ τ₂) f ↔ ∀ j ≤ k, ∀ a, V j τ₁ a →
    (call j f a).2 ≤ j ∧ ((call j f a).1 = .timeout ∨
      (∃ v, (call j f a).1 = .ok v ∧ V (call j f a).2 τ₂ v) ∨
      (∃ v, (call j f a).1 = .thrown v) ∨ (∃ v, (call j f a).1 = .returned v ∧ False)) :=
  Iff.rfl

/-- The builtins' types, which their soundness proofs establish. -/
example : builtinCtx =
    [⟨1, .arrow (.bound 0) .boolean, []⟩, .mono (.arrow .number .number)] := rfl

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
