import Inty.Semantics

/-!
# The clock

`run` never gives back more clock than it was given (`run_clock_le`), and
more clock never changes a result that didn't run out (`run_mono`): the
result is the same, with the extra ticks left over. So a verdict of the
model (`value` or `stuck`) doesn't depend on the clock it was run with,
which is what lets the differential test compare it with `dynamics`, whose
fuel counts something else. CakeML's `evaluate_clock` and
`evaluate_add_to_clock` are the same two facts.
-/

namespace Inty

theorem bindC_le {p : Result × Nat} {K : Value → Nat → Result × Nat} {c : Nat}
    (hp : p.2 ≤ c) (hK : ∀ v, p.1 = .ok v → (K v p.2).2 ≤ c) : (bindC p K).2 ≤ c := by
  obtain ⟨r, c'⟩ := p
  cases r <;> simp_all [bindC]

/-- The clock only runs down. -/
theorem run_clock_le (c : Nat) (env : Env) (e : Expr) : (run c env e).2 ≤ c := by
  induction c, env, e using run.induct with
  | case5 clock env f a ihf iha ihb =>
    rw [run_app]
    refine bindC_le ihf fun vf _ => ?_
    refine bindC_le (Nat.le_trans (iha _) (Nat.min_le_right _ _)) fun va _ => ?_
    generalize hm : min _ clock = m
    cases vf <;> cases m <;> simp only [call] <;> try omega
    exact Nat.le_trans (ihb _ _ _ _ _ _ hm) (by omega)
  | case6 clock env e₁ e₂ ih₁ ih₂ =>
    rw [run]
    exact bindC_le ih₁ fun v _ => Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  | case7 clock env c t e ihc iht ihe =>
    rw [run]
    refine bindC_le ihc fun v _ => ?_
    split
    · exact Nat.le_trans (iht _) (Nat.min_le_right _ _)
    · exact Nat.le_trans (ihe _) (Nat.min_le_right _ _)
  | case8 clock env op e ih => rw [run]; exact bindC_le ih fun _ _ => ih
  | case9 clock env op e₁ e₂ ih₁ ih₂ =>
    rw [run]
    exact bindC_le ih₁ fun _ _ =>
      bindC_le (Nat.le_trans (ih₂ _) (Nat.min_le_right _ _)) fun _ _ =>
        Nat.le_trans (ih₂ _) (Nat.min_le_right _ _)
  | case10 clock env e ih => rw [run]; exact bindC_le ih fun _ _ => ih
  | case11 clock env e ih => rw [run]; exact bindC_le ih fun _ _ => ih
  | case12 clock env e₁ e₂ ih₁ ih₂ =>
    rw [run]
    exact bindC_le ih₁ fun _ _ => Nat.le_trans (ih₂ _) (Nat.min_le_right _ _)
  | _ => simp_all [run]

/-- If more clock doesn't change `p` unless it timed out, nor `K`'s results,
then it doesn't change `bindC p K` unless that timed out. -/
theorem bindC_mono {p p' : Result × Nat} {K K' : Value → Nat → Result × Nat} {k : Nat}
    (hp : p.1 ≠ .timeout → p' = (p.1, p.2 + k))
    (hK : ∀ v, p.1 = .ok v → (K v p.2).1 ≠ .timeout →
      K' v (p.2 + k) = ((K v p.2).1, (K v p.2).2 + k))
    (h : (bindC p K).1 ≠ .timeout) : bindC p' K' = ((bindC p K).1, (bindC p K).2 + k) := by
  obtain ⟨r, c'⟩ := p
  cases r with
  | ok v => rw [hp (by simp)]; exact hK v rfl h
  | timeout => simp [bindC] at h
  | _ => rw [hp (by simp)]; rfl

/-- More clock: the same result, with the extra ticks left over. -/
theorem run_mono (c : Nat) (env : Env) (e : Expr) :
    ∀ k, (run c env e).1 ≠ .timeout → run (c + k) env e = ((run c env e).1, (run c env e).2 + k) := by
  induction c, env, e using run.induct with
  | case5 clock env f a ihf iha ihb =>
    intro k h
    simp only [run_app] at h ⊢
    refine bindC_mono (ihf k) (fun vf _ h => ?_) h
    have hc₁ := run_clock_le clock env f
    have iha' := iha (run clock env f).2
    rw [Nat.min_eq_left hc₁] at iha'
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindC_mono (iha' k) (fun va _ h => ?_) h
    have hc₂ : (run (run clock env f).snd env a).snd ≤ clock :=
      Nat.le_trans (run_clock_le _ env a) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    generalize (run (run clock env f).snd env a).snd = c₂ at *
    cases vf with
    | closure cenv body =>
      cases c₂ with
      | zero => simp [call] at h
      | succ c =>
        have hb : (run c (va :: .closure cenv body :: cenv) body).1 ≠ .timeout := by
          intro hb; apply h; simp [call, hb, Result.catchReturn]
        rw [show c + 1 + k = (c + k) + 1 by omega]
        simp only [call, ihb _ va (c + 1) cenv body c (Nat.min_eq_left hc₂) k hb]
    | _ => rfl
  | case6 clock env e₁ e₂ ih₁ ih₂ =>
    intro k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env e₁
    have ih₂' := ih₂ v (run clock env e₁).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact ih₂' k h
  | case7 clock env c t e ihc iht ihe =>
    intro k h
    simp only [run] at h ⊢
    refine bindC_mono (ihc k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env c
    have iht' := iht (run clock env c).2
    have ihe' := ihe (run clock env c).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h iht' ihe' ⊢
    split at h
    · rename_i hv; simp only [hv, ite_true]; exact iht' k h
    · rename_i hv; simp only [hv]; exact ihe' k h
  | case8 clock env op e ih =>
    intro k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  | case9 clock env op e₁ e₂ ih₁ ih₂ =>
    intro k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env e₁
    have ih₂' := ih₂ (run clock env e₁).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact bindC_mono (ih₂' k) (fun _ _ _ => rfl) h
  | case10 clock env e ih =>
    intro k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  | case11 clock env e ih =>
    intro k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  | case12 clock env e₁ e₂ ih₁ ih₂ =>
    intro k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env e₁
    have ih₂' := ih₂ (run clock env e₁).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact ih₂' k h
  | _ => intro k h; simp_all [run]

/-- More clock never changes a result that didn't run out. -/
theorem eval_mono (c : Nat) {env : Env} {e : Expr} (k : Nat) (h : eval c env e ≠ .timeout) :
    eval (c + k) env e = eval c env e := by
  simp only [eval, run_mono c env e k h]

/-- Any two clocks that both finish agree. -/
theorem eval_clock_agree {n m : Nat} (hn : eval n env e ≠ .timeout)
    (hm : eval m env e ≠ .timeout) : eval n env e = eval m env e := by
  rcases Nat.le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact (eval_mono n k hn).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; exact eval_mono m k hm

end Inty
