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

theorem bindArgs_le {p : Except Result (List Value) × Nat} {K : List Value → Nat → Result × Nat}
    {c : Nat} (hp : p.2 ≤ c) (hK : ∀ vs, p.1 = .ok vs → (K vs p.2).2 ≤ c) :
    (bindArgs p K).2 ≤ c := by
  obtain ⟨r, c'⟩ := p
  cases r <;> simp_all [bindArgs]

/-- The clock only runs down, for `run` and for `runArgs`. -/
theorem run_clock_le_both :
    (∀ c env e, (run c env e).2 ≤ c) ∧ (∀ c env es, (runArgs c env es).2 ≤ c) := by
  refine run.mutual_induct (fun c env e => (run c env e).2 ≤ c)
    (fun c env es => (runArgs c env es).2 ≤ c) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros; simp [run]
  · intro _ _ _ _ h; simp [run, h]
  · intro _ _ _ h; simp [run, h]
  · intros; simp [run]
  · intro clock env f args ihf iha ihb
    rw [run_app]
    refine bindC_le ihf fun vf _ => ?_
    refine bindArgs_le (Nat.le_trans (iha _) (Nat.min_le_right _ _)) fun vs _ => ?_
    generalize hm : min _ clock = m
    cases vf <;> simp only [call] <;> try omega
    split <;> try omega
    cases m <;> try (simp only; omega)
    exact Nat.le_trans (ihb _ _ _ _ 0 _ _ hm) (by omega)
  · intro clock env e₁ e₂ ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun v _ => Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  · intro clock env c t e ihc iht ihe
    rw [run]
    refine bindC_le ihc fun v _ => ?_
    split
    · exact Nat.le_trans (iht _) (Nat.min_le_right _ _)
    · exact Nat.le_trans (ihe _) (Nat.min_le_right _ _)
  · intro clock env op e ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env op e₁ e₂ ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun _ _ =>
      bindC_le (Nat.le_trans (ih₂ _) (Nat.min_le_right _ _)) fun _ _ =>
        Nat.le_trans (ih₂ _) (Nat.min_le_right _ _)
  · intro clock env e ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env e ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env e₁ e₂ ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun _ _ => Nat.le_trans (ih₂ _) (Nat.min_le_right _ _)
  · intros; simp [runArgs]
  · intro clock env e es v c₁ hrun vs c hargs ih₁ ih₂
    rw [hargs] at ih₂
    simp only [runArgs, hrun, hargs]
    simp only at ih₂; omega
  · intro clock env e es v c₁ hrun r c hargs ih₁ ih₂
    rw [hargs] at ih₂
    simp only [runArgs, hrun, hargs]
    simp only at ih₂; omega
  · intro clock env e es r c₁ hr hrun ih₁
    rw [hrun] at ih₁
    simp only [runArgs, hrun]
    simpa using ih₁

theorem run_clock_le (c : Nat) (env : Env) (e : Expr) : (run c env e).2 ≤ c :=
  run_clock_le_both.1 c env e

theorem runArgs_clock_le (c : Nat) (env : Env) (es : List Expr) : (runArgs c env es).2 ≤ c :=
  run_clock_le_both.2 c env es

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

theorem bindArgs_mono {p p' : Except Result (List Value) × Nat}
    {K K' : List Value → Nat → Result × Nat} {k : Nat}
    (hp : p.1 ≠ .error .timeout → p' = (p.1, p.2 + k))
    (hK : ∀ vs, p.1 = .ok vs → (K vs p.2).1 ≠ .timeout →
      K' vs (p.2 + k) = ((K vs p.2).1, (K vs p.2).2 + k))
    (h : (bindArgs p K).1 ≠ .timeout) :
    bindArgs p' K' = ((bindArgs p K).1, (bindArgs p K).2 + k) := by
  obtain ⟨r, c'⟩ := p
  cases r with
  | ok vs => rw [hp (by simp)]; exact hK vs rfl h
  | error r =>
    have hr : r ≠ .timeout := fun e => h (by simp [bindArgs, e])
    rw [hp (by simpa using hr)]; rfl

/-- More clock: the same result, with the extra ticks left over; for `run`
and for `runArgs`. -/
theorem run_mono_both :
    (∀ c env e k, (run c env e).1 ≠ .timeout →
      run (c + k) env e = ((run c env e).1, (run c env e).2 + k)) ∧
    (∀ c env es k, (runArgs c env es).1 ≠ .error .timeout →
      runArgs (c + k) env es = ((runArgs c env es).1, (runArgs c env es).2 + k)) := by
  refine run.mutual_induct
    (fun c env e => ∀ k, (run c env e).1 ≠ .timeout →
      run (c + k) env e = ((run c env e).1, (run c env e).2 + k))
    (fun c env es => ∀ k, (runArgs c env es).1 ≠ .error .timeout →
      runArgs (c + k) env es = ((runArgs c env es).1, (runArgs c env es).2 + k))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros; simp [run]
  · intro _ _ _ _ h; simp [run, h]
  · intro _ _ _ h; simp [run, h]
  · intros; simp [run]
  · intro clock env f args ihf iha ihb k h
    simp only [run_app] at h ⊢
    refine bindC_mono (ihf k) (fun vf _ h => ?_) h
    have hc₁ := run_clock_le clock env f
    have iha' := iha (run clock env f).2
    rw [Nat.min_eq_left hc₁] at iha'
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindArgs_mono (iha' k) (fun vs _ h => ?_) h
    have hc₂ : (runArgs (run clock env f).2 env args).2 ≤ clock :=
      Nat.le_trans (runArgs_clock_le _ env args) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    generalize (runArgs (run clock env f).snd env args).snd = c₂ at *
    cases vf with
    | closure cenv n body =>
      by_cases hn : vs.length = n
      · cases c₂ with
        | zero => simp [call, hn] at h
        | succ c =>
          have hb : (run c (vs ++ .closure cenv n body :: .undefined :: cenv) body).1 ≠ .timeout := by
            intro hb; apply h; simp [call, hn, hb, Result.catchReturn]
          rw [show c + 1 + k = (c + k) + 1 by omega]
          simp only [call, hn, ite_true, ihb _ vs (c + 1) cenv n body c (Nat.min_eq_left hc₂) k hb]
      · simp [call, hn]
    | _ => rfl
  · intro clock env e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env e₁
    have ih₂' := ih₂ v (run clock env e₁).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact ih₂' k h
  · intro clock env c t e ihc iht ihe k h
    simp only [run] at h ⊢
    refine bindC_mono (ihc k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env c
    have iht' := iht (run clock env c).2
    have ihe' := ihe (run clock env c).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h iht' ihe' ⊢
    split at h
    · rename_i hv; simp only [hv, ite_true]; exact iht' k h
    · rename_i hv; simp only [hv]; exact ihe' k h
  · intro clock env op e ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env op e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env e₁
    have ih₂' := ih₂ (run clock env e₁).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact bindC_mono (ih₂' k) (fun _ _ _ => rfl) h
  · intro clock env e ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env e ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env e₁
    have ih₂' := ih₂ (run clock env e₁).2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact ih₂' k h
  · intros; simp [runArgs]
  · intro clock env e es v c₁ hrun vs c hargs ih₁ ih₂ k _
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env e
    have e₁ := ih₁ k (by simp [hrun])
    rw [hrun] at e₁
    have e₂ := ih₂ k (by simp [hargs])
    rw [hargs, Nat.min_eq_left hc] at e₂
    rw [Nat.min_eq_left hc] at hargs
    simp only [runArgs, hrun, e₁, Nat.min_eq_left hc, hargs,
      Nat.min_eq_left (Nat.add_le_add_right hc k), e₂]
  · intro clock env e es v c₁ hrun r c hargs ih₁ ih₂ k h
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env e
    have e₁ := ih₁ k (by simp [hrun])
    rw [hrun] at e₁
    rw [Nat.min_eq_left hc] at hargs ih₂
    have hr : r ≠ .timeout := fun hr => h (by simp [runArgs, hrun, Nat.min_eq_left hc, hargs, hr])
    have e₂ := ih₂ k (by simpa [hargs] using hr)
    rw [hargs] at e₂
    simp only [runArgs, hrun, e₁, hargs, Nat.min_eq_left hc,
      Nat.min_eq_left (Nat.add_le_add_right hc k), e₂]
  · intro clock env e es r c₁ hr hrun ih₁ k h
    have hrt : r ≠ .timeout := fun hrt => h (by
      subst hrt; simp [runArgs, hrun])
    have e₁ := ih₁ k (by simpa [hrun] using hrt)
    rw [hrun] at e₁
    cases r with
    | ok v => exact absurd rfl (hr v)
    | _ => simp [runArgs, hrun, e₁]

theorem run_mono (c : Nat) (env : Env) (e : Expr) :
    ∀ k, (run c env e).1 ≠ .timeout → run (c + k) env e = ((run c env e).1, (run c env e).2 + k) :=
  run_mono_both.1 c env e

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
