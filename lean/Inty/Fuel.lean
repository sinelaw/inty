import Inty.Semantics

/-!
# Fuel

More fuel never changes a result that didn't run out of fuel: `eval` either
times out or gives the same answer with any larger budget. So a verdict of
the model (`value` or `stuck`) doesn't depend on the fuel it was run with,
which is what lets the differential test compare it with `dynamics`, whose
fuel counts something else.
-/

namespace Inty

/-- If more fuel doesn't change `r` unless it timed out, nor `K`'s results,
then it doesn't change `r.bind K` unless that timed out. -/
theorem Result.bind_mono {r r' : Result} {K K' : Value → Result}
    (hr : r ≠ .timeout → r' = r) (hk : ∀ v, K v ≠ .timeout → K' v = K v)
    (h : r.bind K ≠ .timeout) : r'.bind K' = r.bind K := by
  have hne : r ≠ .timeout := by intro hc; subst hc; exact h rfl
  rw [hr hne]
  cases r with
  | ok v => exact hk v h
  | _ => rfl

theorem Result.catchReturn_mono {r r' : Result} (hr : r ≠ .timeout → r' = r)
    (h : r.catchReturn ≠ .timeout) : r'.catchReturn = r.catchReturn := by
  have hne : r ≠ .timeout := by intro hc; subst hc; exact h rfl
  rw [hr hne]

theorem eval_mono (n : Nat) :
    ∀ {env : Env} {e : Expr} (k : Nat), eval n env e ≠ .timeout →
      eval (n + k) env e = eval n env e := by
  induction n with
  | zero => intro _ _ _ h; simp [eval] at h
  | succ n ih =>
    intro env e k h
    rw [show n + 1 + k = (n + k) + 1 by omega]
    cases e with
    | lit | var | func => rfl
    | app f a =>
      simp only [eval] at h ⊢
      refine Result.bind_mono (ih k) (fun vf h => Result.bind_mono (ih k) (fun va h => ?_) h) h
      cases vf with
      | closure cenv body => exact Result.catchReturn_mono (ih k) h
      | _ => rfl
    | let_ e₁ e₂ =>
      simp only [eval] at h ⊢
      exact Result.bind_mono (ih k) (fun v h => ih k h) h
    | cond c t e =>
      simp only [eval] at h ⊢
      refine Result.bind_mono (ih k) (fun v h => ?_) h
      split
      · rename_i ht; simp only [ht, ite_true] at h; exact ih k h
      · rename_i ht; simp only [ht] at h; exact ih k h
    | unop op e =>
      simp only [eval] at h ⊢
      exact Result.bind_mono (ih k) (fun _ _ => rfl) h
    | binop op e₁ e₂ =>
      simp only [eval] at h ⊢
      exact Result.bind_mono (ih k) (fun v h => Result.bind_mono (ih k) (fun _ _ => rfl) h) h
    | ret e | throw_ e =>
      simp only [eval] at h ⊢
      exact Result.bind_mono (ih k) (fun _ _ => rfl) h
    | seq e₁ e₂ =>
      simp only [eval] at h ⊢
      exact Result.bind_mono (ih k) (fun _ h => ih k h) h

/-- Any two budgets that both finish agree. -/
theorem eval_fuel_agree {n m : Nat} (hn : eval n env e ≠ .timeout)
    (hm : eval m env e ≠ .timeout) : eval n env e = eval m env e := by
  rcases Nat.le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact (eval_mono n k hn).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact eval_mono m k hm

end Inty
