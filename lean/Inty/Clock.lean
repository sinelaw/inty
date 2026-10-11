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

theorem bindFields_le {p : RanFields} {K : List (String × MemberKind × Value) → Nat → Heap → Ran}
    {c : Nat} (hp : p.2.1 ≤ c) (hK : ∀ fs, p.1 = .ok fs → (K fs p.2.1 p.2.2).2.1 ≤ c) :
    (bindFields p K).2.1 ≤ c := by
  obtain ⟨r, c', h⟩ := p
  cases r <;> simp_all [bindFields]

/-- The clock only runs down: for `run` and the functions it calls. -/
theorem lt_min_le {a b : Nat} : min a b ≤ b := Nat.min_le_right _ _

mutual
theorem run_clock_le (clock : Nat) (env : Env) (heap : Heap) (e : Expr) :
    (run clock env heap e).2.1 ≤ clock :=
  match e with
  | .lit _ | .func _ _ | .ctor _ _ | .break_ | .continue_ => by simp [run]
  | .var _ => by rw [run]; split <;> (try split) <;> simp
  | .app f args => by
    rw [run]
    refine bindC_le (run_clock_le clock env heap f) fun vf _ => ?_
    refine bindArgs_le (Nat.le_trans (runArgs_clock_le _ env _ args) lt_min_le) fun vs _ => ?_
    exact Nat.le_trans (call_clock_le _ _ _ _ _) lt_min_le
  | .new_ f args => by
    rw [run]
    refine bindC_le (run_clock_le clock env heap f) fun vf _ => ?_
    refine bindArgs_le (Nat.le_trans (runArgs_clock_le _ env _ args) lt_min_le) fun vs _ => ?_
    have := Nat.le_trans (call_clock_le (min (runArgs (min (run clock env heap f).2.1 clock) env
      (run clock env heap f).2.2 args).2.1 clock) ((runArgs (min (run clock env heap f).2.1 clock)
      env (run clock env heap f).2.2 args).2.2 ++ [.fields []]) vf.asCtor
      (.obj (runArgs (min (run clock env heap f).2.1 clock) env (run clock env heap f).2.2
        args).2.2.length) vs) lt_min_le
    split <;> simp_all
  | .let_ _ _ e₁ e₂ => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e₁) fun v _ =>
      Nat.le_trans (run_clock_le _ _ _ e₂) lt_min_le
  | .assign _ e => by
    rw [run]
    refine bindC_le (run_clock_le clock env heap e) fun v _ => ?_
    split
    · split <;> exact run_clock_le clock env heap e
    · exact run_clock_le clock env heap e
  | .cond c t f => by
    rw [run]
    refine bindC_le (run_clock_le clock env heap c) fun v _ => ?_
    split
    · exact Nat.le_trans (run_clock_le _ _ _ t) lt_min_le
    · exact Nat.le_trans (run_clock_le _ _ _ f) lt_min_le
  | .unop _ e | .ret e | .throw_ e => by
    rw [run]; exact bindC_le (run_clock_le clock env heap e) fun _ _ => run_clock_le clock env heap e
  | .binop _ e₁ e₂ => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e₁) fun _ _ =>
      bindC_le (Nat.le_trans (run_clock_le _ _ _ e₂) lt_min_le) fun _ _ =>
        Nat.le_trans (run_clock_le _ _ _ e₂) lt_min_le
  | .seq e₁ e₂ => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e₁) fun _ _ =>
      Nat.le_trans (run_clock_le _ _ _ e₂) lt_min_le
  | .while_ test body => by
    rw [run_while]
    refine bindC_le (run_clock_le clock env heap test) fun v _ => ?_
    split
    · have hb := Nat.le_trans (run_clock_le (min (run clock env heap test).2.1 clock) env
        (run clock env heap test).2.2 body) lt_min_le
      simp only [loopNext]
      generalize run (min (run clock env heap test).2.1 clock) env (run clock env heap test).2.2
        body = q at hb ⊢
      obtain ⟨r, c₂, h₂⟩ := q
      simp only at hb
      cases r <;> simp only <;> try omega
      all_goals
        split
        · simp
        · rename_i c hc
          exact Nat.le_trans (run_clock_le c env h₂ _) (by omega)
    · simpa using run_clock_le clock env heap test
  | .tryCatch body handler => by
    rw [run]
    have hb := run_clock_le clock env heap body
    generalize hp : run clock env heap body = p at hb ⊢
    obtain ⟨r, c₁, h₁⟩ := p
    simp only at hb
    cases r <;> simp only <;> try omega
    exact Nat.le_trans (run_clock_le _ _ _ handler) lt_min_le
  | .tryFinally body fin => by
    rw [run]
    have hb := run_clock_le clock env heap body
    generalize hp : run clock env heap body = p at hb ⊢
    obtain ⟨r, c₁, h₁⟩ := p
    simp only at hb
    have hf := Nat.le_trans (run_clock_le (min c₁ clock) env h₁ fin) lt_min_le
    cases r <;> simp only <;> try omega
    all_goals
      generalize run (min c₁ clock) env h₁ fin = q at hf ⊢
      obtain ⟨r', c₂, h₂⟩ := q
      cases r' <;> simp_all
  | .obj _ es _ | .arr es => by
    rw [run]
    exact bindArgs_le (runArgs_clock_le clock env heap es) fun _ _ => runArgs_clock_le clock env heap es
  | .cls ls es ks => by
    rw [run]
    refine bindArgs_le (runInits_clock_le clock env heap es ks) fun vs _ => ?_
    split <;> simpa using runInits_clock_le clock env heap es ks
  | .get e l => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e) fun vo _ =>
      Nat.le_trans (getter_clock_le _ _ _ _) lt_min_le
  | .set e l v => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e) fun _ _ =>
      bindC_le (Nat.le_trans (run_clock_le _ _ _ v) lt_min_le) fun _ _ =>
        Nat.le_trans (run_clock_le _ _ _ v) lt_min_le
  | .spread e₁ e₂ => by
    rw [run]
    refine bindC_le (run_clock_le clock env heap e₁) fun v₁ _ => ?_
    refine bindFields_le (Nat.le_trans (own_clock_le _ _ _) lt_min_le) fun fs₁ _ => ?_
    refine bindC_le (Nat.le_trans (run_clock_le _ _ _ e₂) lt_min_le) fun v₂ _ => ?_
    refine bindFields_le (Nat.le_trans (own_clock_le _ _ _) lt_min_le) fun fs₂ _ => ?_
    simp only
    exact Nat.le_trans (own_clock_le _ _ _) lt_min_le
  | .index e i => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e) fun _ _ =>
      bindC_le (Nat.le_trans (run_clock_le _ _ _ i) lt_min_le) fun _ _ =>
        Nat.le_trans (getter_clock_le _ _ _ _) lt_min_le
  | .setIndex e i v => by
    rw [run]
    exact bindC_le (run_clock_le clock env heap e) fun _ _ =>
      bindC_le (Nat.le_trans (run_clock_le _ _ _ i) lt_min_le) fun _ _ =>
        bindC_le (Nat.le_trans (run_clock_le _ _ _ v) lt_min_le) fun _ _ =>
          Nat.le_trans (run_clock_le _ _ _ v) lt_min_le
  | .mcall e l args => by
    rw [run]
    refine bindC_le (run_clock_le clock env heap e) fun vo _ => ?_
    refine bindC_le (Nat.le_trans (getter_clock_le _ _ _ _) lt_min_le) fun vf _ => ?_
    refine bindArgs_le (Nat.le_trans (runArgs_clock_le _ env _ args) lt_min_le) fun vs _ => ?_
    exact Nat.le_trans (call_clock_le _ _ _ _ _) lt_min_le
termination_by (clock, 2 * sizeOf e, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_refl _)) (.inl (by simp <;> omega))
    | exact lex3_left (by omega)

theorem call_clock_le (clock : Nat) (h : Heap) (vf thisv : Value) (args : List Value) :
    (call clock h vf thisv args).2.1 ≤ clock := by
  rw [call.eq_def]
  split
  · exact callClosure_clock_le _ _ _ _ _ _ _ _
  · exact callClosure_clock_le _ _ _ _ _ _ _ _
  · split <;> simp
  · simp
termination_by (clock, 0, 1)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by omega⟩)

theorem callClosure_clock_le (clock : Nat) (h : Heap) (vf : Value) (cenv : Env) (n : Nat)
    (body : Expr) (thisv : Value) (args : List Value) :
    (callClosure clock h vf cenv n body thisv args).2.1 ≤ clock := by
  by_cases hn : n ≤ args.length
  · cases clock with
    | zero => simp [callClosure, hn]
    | succ c =>
      simp only [callClosure, hn, ite_true]
      exact Nat.le_trans (run_clock_le c _ _ _) (Nat.le_succ c)
  · cases clock <;> simp [callClosure, hn]
termination_by (clock, 0, 0)
decreasing_by all_goals exact lex3_left (by omega)

theorem getter_clock_le (clock : Nat) (h : Heap) (vo : Value) (r : Read) :
    (getter clock h vo r).2.1 ≤ clock := by
  cases r with
  | value v => simp [getter]
  | getter g => simp only [getter]; exact call_clock_le _ _ _ _ _
  | fail r => simp [getter]
termination_by (clock, 0, 2)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by omega⟩)

theorem own_clock_le (clock : Nat) (h : Heap) (v : Value) : (own clock h v).2.1 ≤ clock := by
  cases v with
  | obj ℓ =>
    unfold own
    split
    · rename_i fs _
      have := copyOwn_clock_le clock h (.obj ℓ) (dedupLabels fs).reverse
      split <;> simp_all
    · simp
  | _ => simp [own]
termination_by (clock, 1, 0)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inl (by omega))

theorem copyOwn_clock_le (clock : Nat) (h : Heap) (vo : Value)
    (fs : List (String × MemberKind × Value)) : (copyOwn clock h vo fs).2.1 ≤ clock := by
  match fs with
  | [] => simp [copyOwn]
  | (l, m, _) :: fs =>
    rw [copyOwn]
    split
    · have hc := getter_clock_le clock h vo (vo.read h l)
      generalize getter clock h vo (vo.read h l) = q at hc ⊢
      obtain ⟨r, c₁, h₁⟩ := q
      simp only at hc
      cases r
      case ok v =>
        have := Nat.le_trans (copyOwn_clock_le (min c₁ clock) h₁ vo fs) lt_min_le
        simp only; split <;> simp_all
      all_goals simpa using hc
    · exact copyOwn_clock_le clock h vo fs
termination_by (clock, 0, 3 + fs.length)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by simp <;> omega⟩)
    | exact lex3_of (Nat.min_le_right _ _) (.inr ⟨rfl, by simp <;> omega⟩)

theorem runArgs_clock_le (clock : Nat) (env : Env) (heap : Heap) (args : List Expr) :
    (runArgs clock env heap args).2.1 ≤ clock := by
  match args with
  | [] => simp [runArgs]
  | e :: es =>
    rw [runArgs]
    have he := run_clock_le clock env heap e
    generalize run clock env heap e = q at he ⊢
    obtain ⟨r, c₁, h₁⟩ := q
    simp only at he
    cases r
    case ok v =>
      have := Nat.le_trans (runArgs_clock_le (min c₁ clock) env h₁ es) lt_min_le
      simp only; split <;> simp_all
    all_goals simpa using he
termination_by (clock, 2 * sizeOf args, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))

theorem runInits_clock_le (clock : Nat) (env : Env) (heap : Heap) (es : List Expr)
    (ks : List ClassKind) : (runInits clock env heap es ks).2.1 ≤ clock := by
  match es, ks with
  | e :: es, .data :: ks =>
    rw [runInits]
    have he := run_clock_le clock env heap e
    generalize run clock env heap e = q at he ⊢
    obtain ⟨r, c₁, h₁⟩ := q
    simp only at he
    cases r
    case ok v =>
      have := Nat.le_trans (runInits_clock_le (min c₁ clock) (h₁.length :: env) (h₁ ++ [v]) es ks)
        lt_min_le
      simp only; split <;> simp_all
    all_goals simpa using he
  | _ :: es, .arrow :: ks =>
    simp only [runInits]; exact runInits_clock_le clock env heap es ks
  | _ :: es, .method :: ks =>
    simp only [runInits]; exact runInits_clock_le clock env heap es ks
  | _ :: es, .getter :: ks =>
    simp only [runInits]; exact runInits_clock_le clock env heap es ks
  | [], _ => simp [runInits]
  | _ :: _, [] => simp [runInits]
termination_by (clock, 2 * sizeOf es, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))
end

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

def RanFields.addClock (p : RanFields) (k : Nat) : RanFields := (p.1, p.2.1 + k, p.2.2)

theorem bindFields_mono {p p' : RanFields} {K K' : List (String × MemberKind × Value) → Nat → Heap → Ran}
    {k : Nat} (hp : p.1 ≠ .error .timeout → p' = p.addClock k)
    (hK : ∀ fs, p.1 = .ok fs → (K fs p.2.1 p.2.2).1 ≠ .timeout →
      K' fs (p.2.1 + k) p.2.2 = (K fs p.2.1 p.2.2).addClock k)
    (h : (bindFields p K).1 ≠ .timeout) :
    bindFields p' K' = (bindFields p K).addClock k := by
  obtain ⟨r, c', hp'⟩ := p
  cases r with
  | ok fs => rw [hp (by simp)]; exact hK fs rfl h
  | error r =>
    have hr : r ≠ .timeout := fun e => h (by simp [bindFields, e])
    rw [hp (by simpa using hr)]; rfl

/-- Clamping a clock that came back from a subterm, with `k` more. -/
theorem min_add_clamp {a b : Nat} (k : Nat) (h : a ≤ b) : min (a + k) (b + k) = min a b + k := by
  rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.add_le_add_right h k)]

mutual
/-- More clock: the same result and heap, with the extra ticks left over;
for `run` and the functions it calls. -/
theorem run_mono (clock : Nat) (env : Env) (heap : Heap) (e : Expr) (k : Nat)
    (hne : (run clock env heap e).1 ≠ .timeout) :
    run (clock + k) env heap e = (run clock env heap e).addClock k :=
  match e with
  | .lit _ | .func _ _ | .ctor _ _ | .break_ | .continue_ => by simp [run, Ran.addClock]
  | .var _ => by simp only [run]; split <;> (try split) <;> simp [Ran.addClock]
  | .app f args => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap f k) (fun vf _ h => ?_) hne
    have hc₁ := run_clock_le clock env heap f
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindArgs_mono (runArgs_mono _ env _ args k) (fun vs _ h => ?_) h
    have hc₂ := Nat.le_trans (runArgs_clock_le (run clock env heap f).2.1 env
      (run clock env heap f).2.2 args) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    exact call_mono _ _ _ _ _ k h
  | .new_ f args => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap f k) (fun vf _ h => ?_) hne
    have hc₁ := run_clock_le clock env heap f
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindArgs_mono (runArgs_mono _ env _ args k) (fun vs _ h => ?_) h
    have hc₂ := Nat.le_trans (runArgs_clock_le (run clock env heap f).2.1 env
      (run clock env heap f).2.2 args) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    generalize (runArgs (run clock env heap f).2.1 env (run clock env heap f).2.2 args).2.1 = c₂
      at *
    generalize (runArgs (run clock env heap f).2.1 env (run clock env heap f).2.2 args).2.2 = h₂
      at *
    have hcall : (call c₂ (h₂ ++ [.fields []]) vf.asCtor (.obj h₂.length) vs).1 ≠ .timeout := by
      intro ht; apply h
      generalize call c₂ (h₂ ++ [.fields []]) vf.asCtor (.obj h₂.length) vs = q at ht ⊢
      obtain ⟨r, c, hq⟩ := q
      simp only at ht; subst ht; rfl
    rw [call_mono _ _ _ _ _ k hcall]
    generalize call c₂ (h₂ ++ [.fields []]) vf.asCtor (.obj h₂.length) vs = q
    obtain ⟨r, c, hq⟩ := q
    cases r <;> rfl
  | .let_ _ _ e₁ e₂ => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e₁ k) (fun v _ h => ?_) hne
    have hc := run_clock_le clock env heap e₁
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    exact run_mono _ _ _ e₂ k h
  | .assign _ e => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e k) (fun v _ _ => ?_) hne
    split
    · split <;> rfl
    · rfl
  | .cond c t f => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap c k) (fun v _ h => ?_) hne
    have hc := run_clock_le clock env heap c
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    split at h
    · rename_i hv; simp only [hv, ite_true]; exact run_mono _ _ _ t k h
    · rename_i hv; simp only [hv]; exact run_mono _ _ _ f k h
  | .unop _ e | .ret e | .throw_ e => by
    simp only [run] at hne ⊢
    exact bindC_mono (run_mono clock env heap e k) (fun _ _ _ => rfl) hne
  | .binop _ e₁ e₂ => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e₁ k) (fun v _ h => ?_) hne
    have hc := run_clock_le clock env heap e₁
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    exact bindC_mono (run_mono _ _ _ e₂ k) (fun _ _ _ => rfl) h
  | .seq e₁ e₂ => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e₁ k) (fun v _ h => ?_) hne
    have hc := run_clock_le clock env heap e₁
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    exact run_mono _ _ _ e₂ k h
  | .while_ test body => by
    rw [run_while] at hne ⊢
    rw [run_while]
    refine bindC_mono (run_mono clock env heap test k) (fun v _ h => ?_) hne
    have hc := run_clock_le clock env heap test
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    split
    · rename_i hv
      simp only [hv, ite_true] at h
      have hc₂ := run_clock_le (run clock env heap test).2.1 env (run clock env heap test).2.2 body
      have ihb' := run_mono (run clock env heap test).2.1 env (run clock env heap test).2.2 body k
      generalize hq : run (run clock env heap test).2.1 env (run clock env heap test).2.2 body = q
        at h ihb' hc₂ ⊢
      obtain ⟨r, c₂, h₂⟩ := q
      simp only at hc₂
      cases r
      case timeout => simp [loopNext] at h
      case broke => rw [ihb' (by simp)]; rfl
      case ok | continued =>
        rw [ihb' (by simp)]
        simp only [loopNext, Ran.addClock] at h ⊢
        rw [Nat.min_eq_left (show c₂ ≤ clock by omega)] at h ⊢
        rw [Nat.min_eq_left (show c₂ + k ≤ clock + k by omega)]
        cases c₂ with
        | zero => simp at h
        | succ c =>
          rw [show c + 1 + k = (c + k) + 1 by omega]
          exact run_mono c env h₂ (.while_ test body) k h
      all_goals (rw [ihb' (by simp)]; rfl)
    · rfl
  | .tryCatch body handler => by
    have hb := run_clock_le clock env heap body
    have ihb := run_mono clock env heap body k
    simp only [run] at hne ⊢
    generalize hp : run clock env heap body = p at hb hne ihb ⊢
    obtain ⟨r, c₁, h₁⟩ := p
    simp only at hb
    cases r with
    | thrown v =>
      rw [ihb (by simp)]
      simp only [Ran.addClock] at hne ⊢
      rw [min_add_clamp k hb]
      exact run_mono _ _ _ handler k hne
    | timeout => simp at hne
    | _ => rw [ihb (by simp)]; rfl
  | .tryFinally body fin => by
    have hb := run_clock_le clock env heap body
    have ihb := run_mono clock env heap body k
    simp only [run] at hne ⊢
    generalize hp : run clock env heap body = p at hb hne ihb ⊢
    obtain ⟨r, c₁, h₁⟩ := p
    simp only at hb
    have ihf := run_mono (min c₁ clock) env h₁ fin k
    cases r with
    | timeout => simp at hne
    | stuck s => rw [ihb (by simp)]; rfl
    | fault f => rw [ihb (by simp)]; rfl
    | _ =>
      rw [ihb (by simp)]
      simp only [Ran.addClock] at hne ⊢
      rw [min_add_clamp k hb]
      generalize hq : run (min c₁ clock) env h₁ fin = q at hne ihf ⊢
      obtain ⟨r', c₂, h₂⟩ := q
      cases r' with
      | timeout => simp at hne
      | _ => rw [ihf (by simp)]; rfl
  | .obj _ es _ | .arr es => by
    simp only [run] at hne ⊢
    exact bindArgs_mono (runArgs_mono clock env heap es k) (fun _ _ _ => rfl) hne
  | .cls _ es ks => by
    simp only [run] at hne ⊢
    exact bindArgs_mono (runInits_mono clock env heap es ks k) (fun _ _ _ => by split <;> rfl) hne
  | .get e l => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e k) (fun vo _ h => ?_) hne
    have hc := run_clock_le clock env heap e
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    exact getter_mono _ _ _ _ k h
  | .set e l v => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e k) (fun vo _ h => ?_) hne
    have hc := run_clock_le clock env heap e
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    exact bindC_mono (run_mono _ _ _ v k) (fun _ _ _ => rfl) h
  | .spread e₁ e₂ => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e₁ k) (fun v₁ _ h => ?_) hne
    have hc₁ := run_clock_le clock env heap e₁
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindFields_mono (own_mono _ _ _ k) (fun fs₁ _ h => ?_) h
    have hc₂ := Nat.le_trans (own_clock_le (run clock env heap e₁).2.1 (run clock env heap e₁).2.2
      v₁) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    refine bindC_mono (run_mono _ _ _ e₂ k) (fun v₂ _ h => ?_) h
    have hc₃ := Nat.le_trans (run_clock_le (own (run clock env heap e₁).2.1
      (run clock env heap e₁).2.2 v₁).2.1 env (own (run clock env heap e₁).2.1
      (run clock env heap e₁).2.2 v₁).2.2 e₂) hc₂
    simp only [Nat.min_eq_left hc₃, Nat.min_eq_left (Nat.add_le_add_right hc₃ k)] at h ⊢
    exact bindFields_mono (own_mono _ _ _ k) (fun _ _ _ => rfl) h
  | .index e i => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e k) (fun vo _ h => ?_) hne
    have hc := run_clock_le clock env heap e
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    refine bindC_mono (run_mono _ _ _ i k) (fun vi _ h => ?_) h
    have hc₂ := Nat.le_trans (run_clock_le (run clock env heap e).2.1 env
      (run clock env heap e).2.2 i) hc
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    exact getter_mono _ _ _ _ k h
  | .setIndex e i v => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e k) (fun vo _ h => ?_) hne
    have hc := run_clock_le clock env heap e
    simp only [Nat.min_eq_left hc, Nat.min_eq_left (Nat.add_le_add_right hc k)] at h ⊢
    refine bindC_mono (run_mono _ _ _ i k) (fun vi _ h => ?_) h
    have hc₂ := Nat.le_trans (run_clock_le (run clock env heap e).2.1 env
      (run clock env heap e).2.2 i) hc
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    exact bindC_mono (run_mono _ _ _ v k) (fun _ _ _ => rfl) h
  | .mcall e l args => by
    simp only [run] at hne ⊢
    refine bindC_mono (run_mono clock env heap e k) (fun vo _ h => ?_) hne
    have hc₁ := run_clock_le clock env heap e
    simp only [Nat.min_eq_left hc₁, Nat.min_eq_left (Nat.add_le_add_right hc₁ k)] at h ⊢
    refine bindC_mono (getter_mono _ _ _ _ k) (fun vf _ h => ?_) h
    have hc₂ := Nat.le_trans (getter_clock_le (run clock env heap e).2.1 (run clock env heap e).2.2
      vo (vo.read (run clock env heap e).2.2 l)) hc₁
    simp only [Nat.min_eq_left hc₂, Nat.min_eq_left (Nat.add_le_add_right hc₂ k)] at h ⊢
    refine bindArgs_mono (runArgs_mono _ env _ args k) (fun vs _ h => ?_) h
    have hc₃ := Nat.le_trans (runArgs_clock_le (getter (run clock env heap e).2.1
      (run clock env heap e).2.2 vo (vo.read (run clock env heap e).2.2 l)).2.1 env
      (getter (run clock env heap e).2.1 (run clock env heap e).2.2 vo
        (vo.read (run clock env heap e).2.2 l)).2.2 args) hc₂
    simp only [Nat.min_eq_left hc₃, Nat.min_eq_left (Nat.add_le_add_right hc₃ k)] at h ⊢
    exact call_mono _ _ _ _ _ k h
termination_by (clock, 2 * sizeOf e, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.le_trans (run_clock_le _ _ _ _) (Nat.le_refl _)) (.inl (by simp <;> omega))
    | exact lex3_left (by omega)
    | (apply lex3_of _ (.inl (by simp <;> omega)); omega)

theorem call_mono (clock : Nat) (h : Heap) (vf thisv : Value) (args : List Value) (k : Nat)
    (hne : (call clock h vf thisv args).1 ≠ .timeout) :
    call (clock + k) h vf thisv args = (call clock h vf thisv args).addClock k := by
  rw [call.eq_def] at hne ⊢
  rw [call.eq_def]
  split
  · exact callClosure_mono _ _ _ _ _ _ _ _ k hne
  · exact callClosure_mono _ _ _ _ _ _ _ _ k hne
  · rename_i p
    cases clock with
    | zero => simp at hne
    | succ c => rw [show c + 1 + k = (c + k) + 1 by omega]; simp [Ran.addClock]
  · simp [Ran.addClock]
termination_by (clock, 0, 1)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by omega⟩)

theorem callClosure_mono (clock : Nat) (h : Heap) (vf : Value) (cenv : Env) (n : Nat)
    (body : Expr) (thisv : Value) (args : List Value) (k : Nat)
    (hne : (callClosure clock h vf cenv n body thisv args).1 ≠ .timeout) :
    callClosure (clock + k) h vf cenv n body thisv args =
      (callClosure clock h vf cenv n body thisv args).addClock k := by
  by_cases hn : n ≤ args.length
  · cases clock with
    | zero => simp [callClosure, hn] at hne
    | succ c =>
      have hb : (run c (callEnv h n cenv) (h ++ args.take n ++ [vf, thisv]) body).1 ≠ .timeout := by
        intro hb; apply hne; simp only [callClosure, hn, ite_true, hb, Result.catchReturn]
      rw [show c + 1 + k = (c + k) + 1 by omega]
      simp only [callClosure, hn, ite_true, run_mono c _ _ body k hb, Ran.addClock]
  · have hc : ∀ c, callClosure c h vf cenv n body thisv args = (.stuck .arityMismatch, c, h) :=
      fun c => by cases c <;> simp [callClosure, hn]
    rw [hc, hc]; rfl
termination_by (clock, 0, 0)
decreasing_by all_goals exact lex3_left (by omega)

theorem getter_mono (clock : Nat) (h : Heap) (vo : Value) (r : Read) (k : Nat)
    (hne : (getter clock h vo r).1 ≠ .timeout) :
    getter (clock + k) h vo r = (getter clock h vo r).addClock k := by
  cases r with
  | value v => simp [getter, Ran.addClock]
  | getter g => simp only [getter] at hne ⊢; exact call_mono _ _ _ _ _ k hne
  | fail r => simp [getter, Ran.addClock]
termination_by (clock, 0, 2)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by omega⟩)

theorem own_mono (clock : Nat) (h : Heap) (v : Value) (k : Nat)
    (hne : (own clock h v).1 ≠ .error .timeout) :
    own (clock + k) h v = (own clock h v).addClock k := by
  cases v with
  | obj ℓ =>
    unfold own at hne ⊢
    cases hh : h[ℓ]? with
    | some c =>
      cases c with
      | fields fs =>
        simp only [hh] at hne ⊢
        have hcp := copyOwn_mono clock h (.obj ℓ) (dedupLabels fs).reverse k
        generalize copyOwn clock h (.obj ℓ) (dedupLabels fs).reverse = q at hne hcp ⊢
        obtain ⟨r, c, h'⟩ := q
        cases r with
        | ok cs => rw [hcp (by simp)]; rfl
        | error r =>
          have hr : r ≠ .timeout := fun e => hne (by subst e; rfl)
          rw [hcp (by simpa using hr)]; rfl
      | _ => rfl
    | none => rfl
  | _ => unfold own; rfl
termination_by (clock, 1, 0)
decreasing_by all_goals exact lex3_of (Nat.le_refl _) (.inl (by omega))

theorem copyOwn_mono (clock : Nat) (h : Heap) (vo : Value)
    (fs : List (String × MemberKind × Value)) (k : Nat)
    (hne : (copyOwn clock h vo fs).1 ≠ .error .timeout) :
    copyOwn (clock + k) h vo fs = (copyOwn clock h vo fs).addClock k := by
  match fs with
  | [] => simp [copyOwn, RanFields.addClock]
  | (l, m, _) :: fs =>
    simp only [copyOwn] at hne ⊢
    by_cases hm : m.isOwn = true
    · simp only [hm, ite_true] at hne ⊢
      have hc := getter_clock_le clock h vo (vo.read h l)
      have ihc := getter_mono clock h vo (vo.read h l) k
      generalize getter clock h vo (vo.read h l) = q at hne hc ihc ⊢
      obtain ⟨r, c₁, h₁⟩ := q
      simp only at hc
      cases r with
      | ok v =>
        rw [ihc (by simp)]
        simp only [Ran.addClock] at hne ⊢
        rw [min_add_clamp k hc]
        have ih := copyOwn_mono (min c₁ clock) h₁ vo fs k
        generalize copyOwn (min c₁ clock) h₁ vo fs = q at hne ih ⊢
        obtain ⟨r', c, h'⟩ := q
        cases r' with
        | ok cs => rw [ih (by simp)]; rfl
        | error r =>
          have hr : r ≠ .timeout := fun e => hne (by simp [e])
          rw [ih (by simpa using hr)]; rfl
      | timeout => simp at hne
      | _ => rw [ihc (by simp)]; rfl
    · simp only [hm, Bool.false_eq_true, ite_false] at hne ⊢
      exact copyOwn_mono clock h vo fs k hne
termination_by (clock, 0, 3 + fs.length)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inr ⟨rfl, by simp <;> omega⟩)
    | exact lex3_of (Nat.min_le_right _ _) (.inr ⟨rfl, by simp <;> omega⟩)

theorem runArgs_mono (clock : Nat) (env : Env) (heap : Heap) (args : List Expr) (k : Nat)
    (hne : (runArgs clock env heap args).1 ≠ .error .timeout) :
    runArgs (clock + k) env heap args = (runArgs clock env heap args).addClock k := by
  match args with
  | [] => simp [runArgs, RanArgs.addClock]
  | e :: es =>
    simp only [runArgs] at hne ⊢
    have hc := run_clock_le clock env heap e
    have ihe := run_mono clock env heap e k
    generalize run clock env heap e = q at hne hc ihe ⊢
    obtain ⟨r, c₁, h₁⟩ := q
    simp only at hc
    cases r with
    | ok v =>
      rw [ihe (by simp)]
      simp only [Ran.addClock] at hne ⊢
      rw [min_add_clamp k hc]
      have ih := runArgs_mono (min c₁ clock) env h₁ es k
      generalize runArgs (min c₁ clock) env h₁ es = q at hne ih ⊢
      obtain ⟨r', c, h'⟩ := q
      cases r' with
      | ok vs => rw [ih (by simp)]; rfl
      | error r =>
        have hr : r ≠ .timeout := fun e => hne (by simp [e])
        rw [ih (by simpa using hr)]; rfl
    | timeout => simp at hne
    | _ => rw [ihe (by simp)]; rfl
termination_by (clock, 2 * sizeOf args, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))

theorem runInits_mono (clock : Nat) (env : Env) (heap : Heap) (es : List Expr)
    (ks : List ClassKind) (k : Nat) (hne : (runInits clock env heap es ks).1 ≠ .error .timeout) :
    runInits (clock + k) env heap es ks = (runInits clock env heap es ks).addClock k := by
  match es, ks with
  | e :: es, .data :: ks =>
    simp only [runInits] at hne ⊢
    have hc := run_clock_le clock env heap e
    have ihe := run_mono clock env heap e k
    generalize run clock env heap e = q at hne hc ihe ⊢
    obtain ⟨r, c₁, h₁⟩ := q
    simp only at hc
    cases r with
    | ok v =>
      rw [ihe (by simp)]
      simp only [Ran.addClock] at hne ⊢
      rw [min_add_clamp k hc]
      have ih := runInits_mono (min c₁ clock) (h₁.length :: env) (h₁ ++ [v]) es ks k
      generalize runInits (min c₁ clock) (h₁.length :: env) (h₁ ++ [v]) es ks = q at hne ih ⊢
      obtain ⟨r', c, h'⟩ := q
      cases r' with
      | ok vs => rw [ih (by simp)]; rfl
      | error r =>
        have hr : r ≠ .timeout := fun e => hne (by simp [e])
        rw [ih (by simpa using hr)]; rfl
    | timeout => simp at hne
    | _ => rw [ihe (by simp)]; rfl
  | _ :: es, .arrow :: ks =>
    simp only [runInits] at hne ⊢; exact runInits_mono clock env heap es ks k hne
  | _ :: es, .method :: ks =>
    simp only [runInits] at hne ⊢; exact runInits_mono clock env heap es ks k hne
  | _ :: es, .getter :: ks =>
    simp only [runInits] at hne ⊢; exact runInits_mono clock env heap es ks k hne
  | [], _ => simp [runInits, RanArgs.addClock]
  | _ :: _, [] => simp [runInits, RanArgs.addClock]
termination_by (clock, 2 * sizeOf es, 0)
decreasing_by
  all_goals first
    | exact lex3_of (Nat.le_refl _) (.inl (by simp <;> omega))
    | exact lex3_of (Nat.min_le_right _ _) (.inl (by simp <;> omega))
end

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
