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

theorem bindC_le {p : Ran} {K : Value → Nat → Heap → Ran} {c : Nat}
    (hp : p.2.1 ≤ c) (hK : ∀ v, p.1 = .ok v → (K v p.2.1 p.2.2).2.1 ≤ c) :
    (bindC p K).2.1 ≤ c := by
  obtain ⟨r, c', h⟩ := p
  cases r <;> simp_all [bindC]

theorem bindArgs_le {p : RanArgs} {K : List Value → Nat → Heap → Ran}
    {c : Nat} (hp : p.2.1 ≤ c) (hK : ∀ vs, p.1 = .ok vs → (K vs p.2.1 p.2.2).2.1 ≤ c) :
    (bindArgs p K).2.1 ≤ c := by
  obtain ⟨r, c', h⟩ := p
  cases r <;> simp_all [bindArgs]

/-- The clock only runs down, for `run` and for `runArgs`. -/
theorem run_clock_le_both :
    (∀ c env h e, (run c env h e).2.1 ≤ c) ∧ (∀ c env h es, (runArgs c env h es).2.1 ≤ c) := by
  refine run.mutual_induct (fun c env h e => (run c env h e).2.1 ≤ c)
    (fun c env h es => (runArgs c env h es).2.1 ≤ c)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · intros; simp [run]
  · intro _ _ _ _ _ h₁ _ h₂; simp [run, h₁, h₂]
  · intro _ _ _ _ _ h₁ h₂; simp [run, h₁, h₂]
  · intro _ _ _ _ h; simp [run, h]
  · intros; simp [run]
  · intro clock env heap f args ihf iha ihb
    rw [run_app]
    refine bindC_le ihf fun vf _ => ?_
    refine bindArgs_le (Nat.le_trans (iha _ _) (Nat.min_le_right _ _)) fun vs _ => ?_
    generalize hm : min _ clock = m
    cases vf <;> simp only [call] <;> try omega
    · split
      · cases m <;> try (simp only; omega)
        exact Nat.le_trans (ihb _ _ _ _ _ _ _ _ hm) (by omega)
      · simp only; omega
    · cases m <;> simp only <;> omega
  · intro clock env heap _ e₁ e₂ ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun v _ => Nat.le_trans (ih₂ _ _ _) (Nat.min_le_right _ _)
  · intro clock env heap i e ih
    rw [run]
    refine bindC_le ih fun v _ => ?_
    split
    · split <;> exact ih
    · exact ih
  · intro clock env heap c t e ihc iht ihe
    rw [run]
    refine bindC_le ihc fun v _ => ?_
    split
    · exact Nat.le_trans (iht _ _) (Nat.min_le_right _ _)
    · exact Nat.le_trans (ihe _ _) (Nat.min_le_right _ _)
  · intro clock env heap op e ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env heap op e₁ e₂ ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun _ _ =>
      bindC_le (Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)) fun _ _ =>
        Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  · intro clock env heap e ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env heap e ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env heap e₁ e₂ ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun _ _ => Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  · intro clock env heap test body iht ihb ihw
    rw [run]
    refine bindC_le iht fun v _ => ?_
    have hb := ihb (run clock env heap test).2.1 (run clock env heap test).2.2
    split
    · generalize run (min (run clock env heap test).2.1 clock) env (run clock env heap test).2.2
        body = p at hb ⊢
      obtain ⟨r, c₂, h₂⟩ := p
      simp only at hb
      cases r
      case broke => simp only; omega
      case ok | continued =>
        simp only
        split
        · simp
        · rename_i c hm; exact Nat.le_trans (ihw _ _ c hm) (by omega)
      all_goals simp only; omega
    · simp only; exact iht
  · intros; simp [run]
  · intros; simp [run]
  · intro clock env heap body handler v c₁ h₁ hrun ihb ihh
    rw [hrun] at ihb
    simp only [run, hrun]
    exact Nat.le_trans ihh (Nat.min_le_right _ _)
  · intro clock env heap body handler hnot ihb
    rw [run]
    generalize hp : run clock env heap body = p at ihb hnot
    obtain ⟨r, c₁, h₁⟩ := p
    cases r
    case thrown v => exact absurd rfl (hnot v c₁ h₁)
    all_goals exact ihb
  · intro clock env heap body fin c₁ h₁ hrun ihb
    rw [hrun] at ihb
    simp only [run, hrun]; exact ihb
  · intro clock env heap body fin s c₁ h₁ hrun ihb
    rw [hrun] at ihb
    simp only [run, hrun]; exact ihb
  · intro clock env heap body fin f c₁ h₁ hrun ihb
    rw [hrun] at ihb
    simp only [run, hrun]; exact ihb
  · intro clock env heap body fin r c₁ h₁ hr hst hfa hrun v c h hfin ihb ihf
    rw [hfin] at ihf
    rw [hrun] at ihb
    rw [run, hrun]
    simp only at ihf ihb
    cases r
    case timeout => exact absurd rfl hr
    case stuck s => exact absurd rfl (hst s)
    case fault f => exact absurd rfl (hfa f)
    all_goals (simp only; rw [hfin]; simp only; omega)
  · intro clock env heap body fin r c₁ h₁ hr hst hfa hrun hfin ihb ihf
    rw [run, hrun]
    cases r
    case timeout => exact absurd rfl hr
    case stuck s => exact absurd rfl (hst s)
    case fault f => exact absurd rfl (hfa f)
    all_goals
      simp only
      generalize hq : run (min c₁ clock) env h₁ fin = q at ihf hfin ⊢
      obtain ⟨r', c₂, h₂⟩ := q
      simp only at ihf
      cases r'
      case ok v => exact absurd rfl (hfin v c₂ h₂)
      all_goals simp only; omega
  · intro clock env heap ls es ih
    rw [run]; exact bindArgs_le ih fun _ _ => ih
  · intro clock env heap e l ih; rw [run]; exact bindC_le ih fun _ _ => ih
  · intro clock env heap e l v ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun _ _ =>
      bindC_le (Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)) fun _ _ =>
        Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  · intro clock env heap e₁ e₂ ih₁ ih₂
    rw [run]
    refine bindC_le ih₁ fun _ _ => ?_
    split
    · exact ih₁
    · exact bindC_le (Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)) fun _ _ => by
        split <;> exact Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  · intro clock env heap es ih
    rw [run]; exact bindArgs_le ih fun _ _ => ih
  · intro clock env heap e i ih₁ ih₂
    rw [run]
    exact bindC_le ih₁ fun _ _ =>
      bindC_le (Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)) fun _ _ =>
        Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)
  · intro clock env heap e i v ih₁ ih₂ ih₃
    rw [run]
    exact bindC_le ih₁ fun _ _ =>
      bindC_le (Nat.le_trans (ih₂ _ _) (Nat.min_le_right _ _)) fun _ _ =>
        bindC_le (Nat.le_trans (ih₃ _ _) (Nat.min_le_right _ _)) fun _ _ =>
          Nat.le_trans (ih₃ _ _) (Nat.min_le_right _ _)
  · intros; simp [runArgs]
  · intro clock env heap e es v c₁ h₁ hrun vs c h hargs ih₁ ih₂
    rw [hargs] at ih₂
    simp only [runArgs, hrun, hargs]
    simp only at ih₂; omega
  · intro clock env heap e es v c₁ h₁ hrun r c h hargs ih₁ ih₂
    rw [hargs] at ih₂
    simp only [runArgs, hrun, hargs]
    simp only at ih₂; omega
  · intro clock env heap e es r c₁ h₁ hr hrun ih₁
    rw [hrun] at ih₁
    simp only [runArgs, hrun]
    cases r <;> first | exact absurd rfl (hr _) | simpa using ih₁

theorem run_clock_le (c : Nat) (env : Env) (h : Heap) (e : Expr) : (run c env h e).2.1 ≤ c :=
  run_clock_le_both.1 c env h e

theorem runArgs_clock_le (c : Nat) (env : Env) (h : Heap) (es : List Expr) :
    (runArgs c env h es).2.1 ≤ c :=
  run_clock_le_both.2 c env h es

/-- `p` with `k` more ticks left. -/
def Ran.addClock (p : Ran) (k : Nat) : Ran := (p.1, p.2.1 + k, p.2.2)

def RanArgs.addClock (p : RanArgs) (k : Nat) : RanArgs := (p.1, p.2.1 + k, p.2.2)

/-- If more clock doesn't change `p` unless it timed out, nor `K`'s results,
then it doesn't change `bindC p K` unless that timed out. -/
theorem bindC_mono {p p' : Ran} {K K' : Value → Nat → Heap → Ran} {k : Nat}
    (hp : p.1 ≠ .timeout → p' = p.addClock k)
    (hK : ∀ v, p.1 = .ok v → (K v p.2.1 p.2.2).1 ≠ .timeout →
      K' v (p.2.1 + k) p.2.2 = (K v p.2.1 p.2.2).addClock k)
    (h : (bindC p K).1 ≠ .timeout) : bindC p' K' = (bindC p K).addClock k := by
  obtain ⟨r, c', hp'⟩ := p
  cases r with
  | ok v => rw [hp (by simp)]; exact hK v rfl h
  | timeout => simp [bindC] at h
  | _ => rw [hp (by simp)]; rfl

theorem bindArgs_mono {p p' : RanArgs} {K K' : List Value → Nat → Heap → Ran} {k : Nat}
    (hp : p.1 ≠ .error .timeout → p' = p.addClock k)
    (hK : ∀ vs, p.1 = .ok vs → (K vs p.2.1 p.2.2).1 ≠ .timeout →
      K' vs (p.2.1 + k) p.2.2 = (K vs p.2.1 p.2.2).addClock k)
    (h : (bindArgs p K).1 ≠ .timeout) :
    bindArgs p' K' = (bindArgs p K).addClock k := by
  obtain ⟨r, c', hp'⟩ := p
  cases r with
  | ok vs => rw [hp (by simp)]; exact hK vs rfl h
  | error r =>
    have hr : r ≠ .timeout := fun e => h (by simp [bindArgs, e])
    rw [hp (by simpa using hr)]; rfl

/-- More clock: the same result and heap, with the extra ticks left over;
for `run` and for `runArgs`. -/
theorem run_mono_both :
    (∀ c env h e k, (run c env h e).1 ≠ .timeout →
      run (c + k) env h e = (run c env h e).addClock k) ∧
    (∀ c env h es k, (runArgs c env h es).1 ≠ .error .timeout →
      runArgs (c + k) env h es = (runArgs c env h es).addClock k) := by
  refine run.mutual_induct
    (fun c env h e => ∀ k, (run c env h e).1 ≠ .timeout →
      run (c + k) env h e = (run c env h e).addClock k)
    (fun c env h es => ∀ k, (runArgs c env h es).1 ≠ .error .timeout →
      runArgs (c + k) env h es = (runArgs c env h es).addClock k)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · intros; simp [run, Ran.addClock]
  · intro _ _ _ _ _ h₁ _ h₂; simp [run, h₁, h₂, Ran.addClock]
  · intro _ _ _ _ _ h₁ h₂; simp [run, h₁, h₂, Ran.addClock]
  · intro _ _ _ _ h; simp [run, h, Ran.addClock]
  · intros; simp [run, Ran.addClock]
  · intro clock env heap f args ihf iha ihb k h
    simp only [run_app] at h ⊢
    refine bindC_mono (ihf k) (fun vf _ h => ?_) h
    have hc₁ := run_clock_le clock env heap f
    have iha' := iha (run clock env heap f).2.1 (run clock env heap f).2.2
    rw [Nat.min_eq_left hc₁] at iha'
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindArgs_mono (iha' k) (fun vs _ h => ?_) h
    have hc₂ : (runArgs (run clock env heap f).2.1 env (run clock env heap f).2.2 args).2.1 ≤
        clock := Nat.le_trans (runArgs_clock_le _ env _ args) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    generalize (runArgs (run clock env heap f).2.1 env (run clock env heap f).2.2 args).2.1 = c₂
      at *
    generalize (runArgs (run clock env heap f).2.1 env (run clock env heap f).2.2 args).2.2 = h₂
      at *
    cases vf with
    | closure cenv n body =>
      by_cases hn : n ≤ vs.length
      · cases c₂ with
        | zero => simp [call, hn] at h
        | succ c =>
          have hb : (run c (callEnv h₂ n cenv)
              (h₂ ++ vs.take n ++ [.closure cenv n body, .undefined]) body).1 ≠ .timeout := by
            intro hb; apply h; simp only [call, hn, ite_true, hb, Result.catchReturn]
          rw [show c + 1 + k = (c + k) + 1 by omega]
          simp only [call, hn, ite_true,
            ihb _ vs (c + 1) h₂ cenv n body c (Nat.min_eq_left hc₂) k hb, Ran.addClock]
      · simp [call, hn, Ran.addClock]
    | prim p =>
      cases c₂ with
      | zero => simp [call] at h
      | succ c =>
        rw [show c + 1 + k = (c + k) + 1 by omega]
        simp [call, Ran.addClock]
    | _ => rfl
  · intro clock env heap _ e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env heap e₁
    have ih₂' := ih₂ v (run clock env heap e₁).2.1 (run clock env heap e₁).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact ih₂' k h
  · intro clock env heap i e ih k h
    simp only [run] at h ⊢
    refine bindC_mono (ih k) (fun v _ _ => ?_) h
    split
    · split <;> rfl
    · rfl
  · intro clock env heap c t e ihc iht ihe k h
    simp only [run] at h ⊢
    refine bindC_mono (ihc k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env heap c
    have iht' := iht (run clock env heap c).2.1 (run clock env heap c).2.2
    have ihe' := ihe (run clock env heap c).2.1 (run clock env heap c).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h iht' ihe' ⊢
    split at h
    · rename_i hv; simp only [hv, ite_true]; exact iht' k h
    · rename_i hv; simp only [hv]; exact ihe' k h
  · intro clock env heap op e ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env heap op e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env heap e₁
    have ih₂' := ih₂ (run clock env heap e₁).2.1 (run clock env heap e₁).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact bindC_mono (ih₂' k) (fun _ _ _ => rfl) h
  · intro clock env heap e ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env heap e ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env heap e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env heap e₁
    have ih₂' := ih₂ (run clock env heap e₁).2.1 (run clock env heap e₁).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact ih₂' k h
  · intro clock env heap test body iht ihb ihw k h
    rw [run_while] at h ⊢
    rw [run_while]
    refine bindC_mono (iht k) (fun v _ h => ?_) h
    have hc := run_clock_le clock env heap test
    have ihb' := ihb (run clock env heap test).2.1 (run clock env heap test).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ihb' ⊢
    split
    · rename_i hv
      simp only [hv, ite_true] at h
      have hc₂ := run_clock_le (run clock env heap test).2.1 env (run clock env heap test).2.2 body
      generalize hq : run (run clock env heap test).2.1 env (run clock env heap test).2.2 body = q
        at h ihb' hc₂ ⊢
      obtain ⟨r, c₂, h₂⟩ := q
      simp only at hc₂
      cases r
      case timeout => simp [loopNext] at h
      case broke => rw [ihb' k (by simp)]; rfl
      case ok | continued =>
        rw [ihb' k (by simp)]
        simp only [loopNext, Ran.addClock] at h ⊢
        rw [Nat.min_eq_left (show c₂ ≤ clock by omega)] at h ⊢
        rw [Nat.min_eq_left (show c₂ + k ≤ clock + k by omega)]
        cases c₂ with
        | zero => simp at h
        | succ c =>
          rw [show c + 1 + k = (c + k) + 1 by omega]
          exact ihw _ _ c (Nat.min_eq_left (show c + 1 ≤ clock by omega)) k h
      all_goals (rw [ihb' k (by simp)]; rfl)
    · rfl
  · intros; simp [run, Ran.addClock]
  · intros; simp [run, Ran.addClock]
  · intro clock env heap body handler v c₁ h₁ hrun ihb ihh k h
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env heap body
    have e₁ := ihb k (by simp [hrun])
    rw [hrun] at e₁
    have ihh' := ihh k
    rw [Nat.min_eq_left hc] at ihh'
    simp only [run, hrun, Nat.min_eq_left hc] at h ⊢
    rw [e₁]
    simp only [Ran.addClock, Nat.min_eq_left (Nat.add_le_add_right hc k)]
    exact ihh' h
  · intro clock env heap body handler hnot ihb k h
    simp only [run] at h ⊢
    generalize hp : run clock env heap body = p at h hnot ihb ⊢
    obtain ⟨r, c₁, h₁⟩ := p
    cases r
    case thrown v => exact absurd rfl (hnot v c₁ h₁)
    case timeout => exact absurd rfl h
    all_goals (rw [ihb k (by simp)]; rfl)
  · intro clock env heap body fin c₁ h₁ hrun ihb k h
    simp [run, hrun] at h
  · intro clock env heap body fin s c₁ h₁ hrun ihb k h
    have e₁ := ihb k (by simp [hrun])
    rw [hrun] at e₁
    simp only [run, hrun, e₁, Ran.addClock]
  · intro clock env heap body fin f c₁ h₁ hrun ihb k h
    have e₁ := ihb k (by simp [hrun])
    rw [hrun] at e₁
    simp only [run, hrun, e₁, Ran.addClock]
  · intro clock env heap body fin r c₁ h₁ hr hst hfa hrun v c h hfin ihb ihf k hne
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env heap body
    have e₁ := ihb k (by simpa [hrun] using hr)
    rw [hrun] at e₁
    have ihf' := ihf k
    rw [Nat.min_eq_left hc] at ihf' hfin
    have e₂ := ihf' (by simp [hfin])
    rw [hfin] at e₂
    simp only [run, hrun, e₁]
    cases r
    case timeout => exact absurd rfl hr
    case stuck s => exact absurd rfl (hst s)
    case fault f => exact absurd rfl (hfa f)
    all_goals
      simp only [Ran.addClock, Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)]
      simp only [Ran.addClock] at e₂
      rw [e₂, hfin]
  · intro clock env heap body fin r c₁ h₁ hr hst hfa hrun hfin ihb ihf k hne
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env heap body
    have e₁ := ihb k (by simpa [hrun] using hr)
    rw [hrun] at e₁
    have ihf' := ihf k
    rw [Nat.min_eq_left hc] at ihf' hfin
    simp only [run, hrun, e₁] at hne ⊢
    cases r
    case timeout => exact absurd rfl hr
    case stuck s => exact absurd rfl (hst s)
    case fault f => exact absurd rfl (hfa f)
    all_goals
      simp only [Ran.addClock, Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)]
        at hne ⊢
      generalize hq : run c₁ env h₁ fin = q at hne hfin ihf' ⊢
      obtain ⟨r', c₂, h₂⟩ := q
      cases r'
      case ok => exact absurd rfl (hfin _ _ _)
      case timeout => simp at hne
      all_goals (rw [ihf' (by simp)]; rfl)
  · intro clock env heap ls es ih k h
    simp only [run] at h ⊢
    exact bindArgs_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env heap e l ih k h
    simp only [run] at h ⊢
    exact bindC_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env heap e l v ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun vo _ h => ?_) h
    have hc := run_clock_le clock env heap e
    have ih₂' := ih₂ (run clock env heap e).2.1 (run clock env heap e).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact bindC_mono (ih₂' k) (fun _ _ _ => rfl) h
  · intro clock env heap e₁ e₂ ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun vo _ h => ?_) h
    have hc := run_clock_le clock env heap e₁
    have ih₂' := ih₂ (run clock env heap e₁).2.1 (run clock env heap e₁).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    cases hf : vo.fieldsOf (run clock env heap e₁).2.2 with
    | none => rfl
    | some fs₁ =>
      simp only [hf] at h ⊢
      exact bindC_mono (ih₂' k) (fun _ _ _ => by split <;> rfl) h
  · intro clock env heap es ih k h
    simp only [run] at h ⊢
    exact bindArgs_mono (ih k) (fun _ _ _ => rfl) h
  · intro clock env heap e i ih₁ ih₂ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun vo _ h => ?_) h
    have hc := run_clock_le clock env heap e
    have ih₂' := ih₂ (run clock env heap e).2.1 (run clock env heap e).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    exact bindC_mono (ih₂' k) (fun _ _ _ => rfl) h
  · intro clock env heap e i v ih₁ ih₂ ih₃ k h
    simp only [run] at h ⊢
    refine bindC_mono (ih₁ k) (fun vo _ h => ?_) h
    have hc := run_clock_le clock env heap e
    have ih₂' := ih₂ (run clock env heap e).2.1 (run clock env heap e).2.2
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ih₂' ⊢
    refine bindC_mono (ih₂' k) (fun vi _ h => ?_) h
    generalize hp : run (run clock env heap e).2.1 env (run clock env heap e).2.2 i = p at h ⊢
    obtain ⟨r₂, c₂, h₂⟩ := p
    have hc₂ : c₂ ≤ (run clock env heap e).2.1 := by
      have := run_clock_le (run clock env heap e).2.1 env (run clock env heap e).2.2 i
      rw [hp] at this; exact this
    simp only at h ⊢
    have hc₂' : c₂ ≤ clock := Nat.le_trans hc₂ hc
    have ih₃' := ih₃ c₂ h₂
    simp only [Nat.min_eq_left hc₂', Nat.min_eq_left (Nat.add_le_add_right hc₂' k)] at h ih₃' ⊢
    exact bindC_mono (ih₃' k) (fun _ _ _ => rfl) h
  · intros; simp [runArgs, RanArgs.addClock]
  · intro clock env heap e es v c₁ h₁ hrun vs c h hargs ih₁ ih₂ k _
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env heap e
    have e₁ := ih₁ k (by simp [hrun])
    rw [hrun] at e₁
    have e₂ := ih₂ k (by simp [hargs])
    rw [hargs, Nat.min_eq_left hc] at e₂
    rw [Nat.min_eq_left hc] at hargs
    simp only [runArgs, hrun, e₁, Ran.addClock, Nat.min_eq_left hc, hargs,
      Nat.min_eq_left (Nat.add_le_add_right hc k), e₂, RanArgs.addClock]
  · intro clock env heap e es v c₁ h₁ hrun r c h hargs ih₁ ih₂ k hne
    have hc : c₁ ≤ clock := by simpa [hrun] using run_clock_le clock env heap e
    have e₁ := ih₁ k (by simp [hrun])
    rw [hrun] at e₁
    rw [Nat.min_eq_left hc] at hargs ih₂
    have hr : r ≠ .timeout := fun hr =>
      hne (by simp [runArgs, hrun, Nat.min_eq_left hc, hargs, hr])
    have e₂ := ih₂ k (by simpa [hargs] using hr)
    rw [hargs] at e₂
    simp only [runArgs, hrun, e₁, Ran.addClock, hargs, Nat.min_eq_left hc,
      Nat.min_eq_left (Nat.add_le_add_right hc k), e₂, RanArgs.addClock]
  · intro clock env heap e es r c₁ h₁ hr hrun ih₁ k hne
    have hrt : r ≠ .timeout := fun hrt => hne (by
      subst hrt; simp [runArgs, hrun])
    have e₁ := ih₁ k (by simpa [hrun] using hrt)
    rw [hrun] at e₁
    cases r with
    | ok v => exact absurd rfl (hr v)
    | _ => simp [runArgs, hrun, e₁, Ran.addClock, RanArgs.addClock]

theorem run_mono (c : Nat) (env : Env) (h : Heap) (e : Expr) :
    ∀ k, (run c env h e).1 ≠ .timeout → run (c + k) env h e = (run c env h e).addClock k :=
  run_mono_both.1 c env h e

/-- More clock never changes a result that didn't run out. -/
theorem eval_mono (c : Nat) {env : Env} {h : Heap} {e : Expr} (k : Nat)
    (hne : eval c env h e ≠ .timeout) : eval (c + k) env h e = eval c env h e := by
  simp only [eval, run_mono c env h e k hne, Ran.addClock]

/-- Any two clocks that both finish agree. -/
theorem eval_clock_agree {n m : Nat} (hn : eval n env h e ≠ .timeout)
    (hm : eval m env h e ≠ .timeout) : eval n env h e = eval m env h e := by
  rcases Nat.le_total n m with hl | hl
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl; exact (eval_mono n k hn).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl; exact eval_mono m k hm

end Inty
