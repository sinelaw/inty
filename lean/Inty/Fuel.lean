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
      have hf : eval n env f ≠ .timeout := fun hc => by simp [hc] at h
      rw [ih k hf]
      split
      · rename_i vf hvf
        rw [hvf] at h
        have ha : eval n env a ≠ .timeout := fun hc => by simp [hc] at h
        rw [ih k ha]
        split
        · rename_i va hva
          rw [hva] at h
          split
          · rename_i cenv body
            exact ih k h
          · rfl
        · rfl
      · rfl
    | let_ e₁ e₂ =>
      simp only [eval] at h ⊢
      have h₁ : eval n env e₁ ≠ .timeout := fun hc => by simp [hc] at h
      rw [ih k h₁]
      split
      · rename_i v hv
        rw [hv] at h
        exact ih k h
      · rfl
    | cond c t e =>
      simp only [eval] at h ⊢
      have hc : eval n env c ≠ .timeout := fun hc' => by simp [hc'] at h
      rw [ih k hc]
      split
      · rename_i v hv
        rw [hv] at h
        split
        · rename_i ht; simp only [ht, ite_true] at h; exact ih k h
        · rename_i ht; simp only [ht] at h; exact ih k h
      · rfl
    | unop op e =>
      simp only [eval] at h ⊢
      have he : eval n env e ≠ .timeout := fun hc => by simp [hc] at h
      rw [ih k he]
    | binop op e₁ e₂ =>
      simp only [eval] at h ⊢
      have h₁ : eval n env e₁ ≠ .timeout := fun hc => by simp [hc] at h
      rw [ih k h₁]
      split
      · rename_i v₁ hv₁
        rw [hv₁] at h
        have h₂ : eval n env e₂ ≠ .timeout := fun hc => by simp [hc] at h
        rw [ih k h₂]
      · rfl

/-- Any two budgets that both finish agree. -/
theorem eval_fuel_agree {n m : Nat} (hn : eval n env e ≠ .timeout)
    (hm : eval m env e ≠ .timeout) : eval n env e = eval m env e := by
  rcases Nat.le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact (eval_mono n k hn).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact eval_mono m k hm

end Inty
