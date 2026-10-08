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

example : ∀ (clock : Nat) {C : List Pred} {Γ : Ctx} {R : Option Ty} {W : World} {env : Env}
    {h : Heap} {e : Expr} {τ : Ty}, HasType C Γ R e τ → Holds C → G W Γ env → HeapOK clock W h →
      (run clock env h e).2.1 ≤ clock ∧
      ((run clock env h e).1 = .timeout ∨ ∃ W', W <+: W' ∧
        HeapOK (run clock env h e).2.1 W' (run clock env h e).2.2 ∧
        ((∃ v, (run clock env h e).1 = .ok v ∧ V (run clock env h e).2.1 W' τ v) ∨
          (run clock env h e).1.Abrupt ∨
          (∃ v, (run clock env h e).1 = .returned v ∧
            ∃ τr, R = some τr ∧ V (run clock env h e).2.1 W' τr v))) :=
  fun clock _ _ _ _ _ _ _ _ ht hC hG hH => eval_sound clock ht hC hG hH

example : ∀ {e : Expr} {τ : Ty}, HasType [] [] none e τ →
    ∀ (clock : Nat) (s : Stuck), eval clock [] [] e ≠ .stuck s :=
  never_stuck

example : ∀ {e : Expr} {τ : Ty}, HasType [] builtinCtx none e τ →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv builtinHeap e ≠ .stuck s :=
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
    ∀ (clock : Nat) (s : Stuck), eval clock [] [] e ≠ .stuck s :=
  inferProgram_never_stuck

example : ∀ {e : Expr} {τ : Ty}, inferIn builtinCtx e = some τ →
    ∀ (clock : Nat) (s : Stuck), eval clock builtinEnv builtinHeap e ≠ .stuck s :=
  inferIn_builtins_never_stuck

example : ∀ (e : Expr) {Γ : Ctx} {R : Option Ty} {n : Nat} {ψ : Subst} {C : List Pred}
    {τ' : Ty} {Γ' : Ctx} {R' : Option Ty},
    Ctx.Below n Γ → Ret.Below n R → (∀ p ∈ C, ∃ a, p = ⟨.plus, [.var a]⟩) →
    Γ' = Ctx.subst ψ Γ → R' = Ret.subst ψ R → HasType C Γ' R' e τ' →
    ∃ o, infer Γ R e n = some o ∧ ∃ φ, Agree n o.σ φ ψ ∧ o.τ.subst φ = τ' ∧ Sat C o.preds φ :=
  infer_complete

example : ∀ {Γ : Ctx} {e : Expr} {τ' : Ty}, ctxFtv Γ = [] →
    e.scoped (Γ.map fun _ => false) = true → HasType [] Γ none e τ' →
    ∃ o, infer Γ none e 0 = some o ∧ (∃ φ, o.τ.subst φ = τ') ∧ ∃ τ, inferIn Γ e = some τ :=
  inferIn_complete

example : ∀ {e : Expr} {τ' : Ty}, e.scoped [] = true → HasType [] [] none e τ' →
    ∃ τ, inferProgram e = some τ :=
  inferProgram_complete

example : ∀ (c : Nat) (env : Env) (h : Heap) (e : Expr), (run c env h e).2.1 ≤ c :=
  run_clock_le

example : ∀ (c : Nat) (env : Env) (h : Heap) (e : Expr) (k : Nat), (run c env h e).1 ≠ .timeout →
    run (c + k) env h e = ((run c env h e).1, (run c env h e).2.1 + k, (run c env h e).2.2) :=
  run_mono

example : ∀ (n : Nat) {env : Env} {h : Heap} {e : Expr} (k : Nat), eval n env h e ≠ .timeout →
    eval (n + k) env h e = eval n env h e :=
  eval_mono

/-! ## The value relation

`eval_sound` is only as strong as `V`: a `V` that holds of everything would
make it trivial. So its clauses are pinned too. -/

example : V k W .number v ↔ ∃ n, v = .number n := V_number
example : V k W .string v ↔ ∃ s, v = .string s := V_string
example : V k W .boolean v ↔ ∃ b, v = .boolean b := V_boolean
example : V k W .undefined v ↔ v = .undefined := V_undefined
example : V k W .null v ↔ v = .null := V_null
example : V k W .unknown v ↔ True := V_unknown
example : V k W (.var a) v ↔ False := V_var
example : Result.Abrupt r ↔ (∃ v, r = .thrown v) ∨ r = .broke ∨ r = .continued := by
  cases r <;> simp [Result.Abrupt]
example : V k W (.fn θ τs ρ) f ↔ ∀ j ≤ k, ∀ W', W <+: W' → ∀ h thisv args,
    (∀ i < j, HeapOK i W' h) → V j W' θ thisv → VList j W' τs args →
    (call j h f thisv args).2.1 ≤ j ∧ ((call j h f thisv args).1 = .timeout ∨
      ((call j h f thisv args).2.1 < j ∧ ∃ W'', W' <+: W'' ∧
        HeapOK (call j h f thisv args).2.1 W'' (call j h f thisv args).2.2 ∧
        ((∃ v, (call j h f thisv args).1 = .ok v ∧ V (call j h f thisv args).2.1 W'' ρ v) ∨
          (call j h f thisv args).1.Abrupt))) := by
  rw [V_fn]
  constructor
  · intro H j hj W' hW h thisv args hh ht ha
    obtain ⟨hc, H | ⟨hlt, W'', hW'', hH, hr⟩⟩ := H j hj W' hW h thisv args hh ht ha
    · exact ⟨hc, .inl H⟩
    · exact ⟨hc, .inr ⟨hlt, W'', hW'', hH hlt, hr.imp (fun ⟨v, e, hv⟩ => ⟨v, e, hv hlt⟩) id⟩⟩
  · intro H j hj W' hW h thisv args hh ht ha
    obtain ⟨hc, H | ⟨hlt, W'', hW'', hH, hr⟩⟩ := H j hj W' hW h thisv args hh ht ha
    · exact ⟨hc, .inl H⟩
    · exact ⟨hc, .inr ⟨hlt, W'', hW'', fun _ => hH,
        hr.imp (fun ⟨v, e, hv⟩ => ⟨v, e, fun _ => hv⟩) id⟩⟩
example : VList k W [] vs ↔ vs = [] := by cases vs <;> simp
example : VList k W (τ :: τs) vs ↔ ∃ v vs', vs = v :: vs' ∧ V k W τ v ∧ VList k W τs vs' := by
  cases vs with
  | nil => simp
  | cons v vs =>
    simp only [VList_cons]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨v, vs, rfl, h₁, h₂⟩, fun ⟨_, _, e, h₁, h₂⟩ => by
      cases e; exact ⟨h₁, h₂⟩⟩
example : HeapOK k W h ↔ h.length = W.length ∧ ∀ (ℓ : Nat) s, W[ℓ]? = some s →
    ∃ v, h[ℓ]? = some v ∧
      ∀ τs, τs.length = s.arity → Holds (s.instPreds τs) → V k W (s.inst τs) v := Iff.rfl
example : G W (s :: Γ) (ℓ :: env) ↔ W[ℓ]? = some s ∧ G W Γ env := Iff.rfl
example : G W [] env ↔ env = [] := by cases env <;> simp [G]

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

/-- `break;` outside a loop is rejected, by the scope check, as JavaScript
rejects it. -/
example : Expr.break_.scoped [] = false := rfl

/-- `const x = 1; x = 2`: assigning to a `const` is rejected, by the scope
check beside the typing rules. -/
example : (Expr.let_ false (num 1) (.assign 0 (num 2))).assignsMutable [] = false := rfl

/-- `x = 1` for a variable whose scheme is polymorphic: an assigned variable
is a monotype. -/
example : ¬ HasType [] [⟨1, .bound 0, []⟩] none (.assign 0 (num 1)) τ := by
  intro h
  cases h with | assign hi ha _ _ => simp at hi; subst hi; simp at ha

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
