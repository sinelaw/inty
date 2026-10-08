import Inty.Builtins
import Inty.InferComplete

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

example : ∀ (clock : Nat) {C : List Pred} {Γ : Ctx} {R : Option Ty} {env : Env} {e : Expr}
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

example : ∀ {C : List Pred} {Γ : Ctx} {R : Option Ty} {e : Expr} {τ : Ty} (σ : Subst),
    HasType C Γ R e τ →
      HasType (C.map (·.subst σ)) (Γ.map (Scheme.subst σ)) (R.map (·.subst σ)) e (τ.subst σ) :=
  fun σ h => h.subst σ

example : ∀ {τ₁ τ₂ : Ty} {σ : Subst}, unify τ₁ τ₂ = some σ → τ₁.subst σ = τ₂.subst σ :=
  unify_sound

example : ∀ {τ₁ τ₂ : Ty} {ψ : Subst}, τ₁.subst ψ = τ₂.subst ψ →
    ∃ σ, unify τ₁ τ₂ = some σ ∧ ∀ τ : Ty, (τ.subst σ).subst ψ = τ.subst ψ :=
  unify_mgu

example : ∀ {e : Expr} {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out},
    infer Γ R e n = some o → ∀ φ C, (∀ c ∈ o.preds, Entails C (c.subst φ)) →
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

example : ∀ {Γ : Ctx} {e : Expr} {τ' : Ty}, ctxFtv Γ = [] → e.letFree = true →
    HasType [] Γ none e τ' →
    ∃ o, infer Γ none e 0 = some o ∧ (∃ φ, o.τ.subst φ = τ') ∧ ∃ τ, inferIn Γ e = some τ :=
  inferIn_complete

example : ∀ {e : Expr} {τ' : Ty}, e.letFree = true → HasType [] [] none e τ' →
    ∃ τ, inferProgram e = some τ :=
  inferProgram_complete

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
example : V k (.fn θ τs ρ) f ↔ ∀ j ≤ k, ∀ thisv args, V j θ thisv → VList j τs args →
    (call j f thisv args).2 ≤ j ∧ ((call j f thisv args).1 = .timeout ∨
      (∃ v, (call j f thisv args).1 = .ok v ∧ V (call j f thisv args).2 ρ v) ∨
      (∃ v, (call j f thisv args).1 = .thrown v) ∨
      (∃ v, (call j f thisv args).1 = .returned v ∧ False)) :=
  Iff.rfl
example : VList k [] vs ↔ vs = [] := by cases vs <;> simp [VList]
example : VList k (τ :: τs) vs ↔ ∃ v vs', vs = v :: vs' ∧ V k τ v ∧ VList k τs vs' := by
  cases vs with
  | nil => simp [VList]
  | cons v vs => exact ⟨fun ⟨h₁, h₂⟩ => ⟨v, vs, rfl, h₁, h₂⟩, fun ⟨_, _, e, h₁, h₂⟩ => by
      cases e; exact ⟨h₁, h₂⟩⟩

/-! ## The class instances

As with `V`, a larger instance table weakens what `eval_sound` says. -/

example : Entails C p ↔ Inst p ∨ p ∈ C := Iff.rfl

example : Inst p ↔ p = ⟨.plus, [.number]⟩ ∨ p = ⟨.plus, [.string]⟩ :=
  ⟨fun h => by cases h <;> simp, fun h => by rcases h with rfl | rfl <;> constructor⟩

/-- The builtins' types, which their soundness proofs establish. -/
example : builtinCtx =
    [⟨1, .fn .undefined [.bound 0] .boolean, []⟩, .mono (.fn .undefined [.number] .number)] :=
  rfl

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
example : ¬ HasType [] [] none (.app (num 1) [num 2]) τ := by
  intro h
  cases h with
  | app hf _ _ => cases hf with | lit hl => cases hl

/-- `(function f(x) { return x; })(1, 2)`: one argument per parameter. -/
example : ¬ HasType [] [] none (.app (.func 1 (.var 0)) [num 1, num 2]) τ := by
  intro h
  cases h with
  | app hf hlen _ => cases hf with | func hn _ => simp at hlen; omega

/-- `(function f() { return -this; })()`: a call outside a receiver makes
`this` `undefined`, which `-` doesn't take. -/
example : ¬ HasType [] [] none (.app (.func 0 (.unop .neg (.var 1))) []) τ := by
  intro h
  cases h with
  | app hf _ _ =>
    cases hf with
    | func hn hb =>
      rw [List.length_eq_zero_iff] at hn; subst hn
      cases hb with
      | unop hop he =>
        cases hop
        generalize hτ : Ty.number = τ' at he
        cases he with
        | var hi _ _ =>
          simp at hi; subst hi
          simp [Scheme.mono, Scheme.inst, Ty.toPTy, PTy.inst] at hτ

end Inty.Statements
