import Inty.TypeSubst
import Inty.Clock

/-!
# Type soundness

A well-typed program never gets stuck: with any clock, `run` either runs out
of clock or returns a value of the expected type. This is the theorem
`src/meta/soundness.rs` tests by sampling ("Whenever inty accepts a program,
the operational semantics must not get stuck on it"), proved for every
program of the calculus.

Values are typed semantically, by what they do rather than by how they were
written: a step-indexed logical relation `V k τ v` (Appel and McAllester,
TOPLAS 2001; Ahmed, ESOP 2006), with the interpreter's clock as the step
index, as in CakeML. A function has type `τ₁ → τ₂` at index `k` when calling
it with any clock `j ≤ k` on any argument of type `τ₁` gives back a result
of type `τ₂`, at the clock left. So a native function (`Prim`), which no
typing derivation describes, has a type all the same (`Inty.Builtins`), and
so will the recursive and mutable values of later steps. The fundamental
lemma (`run_sound`) says a well-typed expression is in the relation.
-/

namespace Inty

/-- Every constraint in `C` is an instance. -/
def Holds (C : List Pred) : Prop := ∀ p ∈ C, Inst p

theorem Holds.append {C D : List Pred} (hC : Holds C) (hD : Holds D) : Holds (C ++ D) :=
  fun c hc => (List.mem_append.mp hc).elim (hC c) (hD c)

theorem Entails.holds {C : List Pred} (hC : Holds C) (h : Entails C p) : Inst p :=
  h.elim id (hC p)

/-- An outcome that isn't stuck, with at most `k` left on the clock: out of
clock, a value satisfying `P`, a `throw` of any value, or a `return` of a
value satisfying `Q`. `P` and `Q` are given the clock left. -/
def Lands (p : Result × Nat) (k : Nat) (P Q : Nat → Value → Prop) : Prop :=
  p.2 ≤ k ∧ (p.1 = .timeout ∨ (∃ v, p.1 = .ok v ∧ P p.2 v) ∨ (∃ v, p.1 = .thrown v) ∨
    (∃ v, p.1 = .returned v ∧ Q p.2 v))

/-- `V k τ v`: the value `v` has type `τ` for `k` more calls. A base type
has its values. A type variable has none: a closed program can't make a
value of a type it knows nothing about. A function type is what calling the
function does. The definition is by recursion on `τ`; the index only says
how far a function's promise reaches. -/
def V : Nat → Ty → Value → Prop
  | _, .number, v => ∃ n, v = .number n
  | _, .string, v => ∃ s, v = .string s
  | _, .boolean, v => ∃ b, v = .boolean b
  | _, .undefined, v => v = .undefined
  | _, .null, v => v = .null
  | _, .var _, _ => False
  | k, .arrow τ₁ τ₂, f => ∀ j ≤ k, ∀ a, V j τ₁ a →
      Lands (call j f a) j (fun c v => V c τ₂ v) (fun _ _ => False)

/-- A value good for `k` calls is good for fewer. -/
theorem V.mono {j k : Nat} (h : j ≤ k) : ∀ {τ : Ty} {v : Value}, V k τ v → V j τ v
  | .arrow _ _, _, hv => fun i hi a ha => hv i (Nat.le_trans hi h) a ha
  | .number, _, hv | .string, _, hv | .boolean, _, hv | .undefined, _, hv | .null, _, hv
  | .var _, _, hv => hv

/-- A safe outcome at `τ`, in a function returning `R`, from a clock of `k`. -/
def Safe (p : Result × Nat) (k : Nat) (τ : Ty) (R : Option Ty) : Prop :=
  Lands p k (fun c v => V c τ v) (fun c v => ∃ τr, R = some τr ∧ V c τr v)

theorem Lands.weaken (h : Lands p c P Q) (hc : c ≤ k) : Lands p k P Q :=
  ⟨Nat.le_trans h.1 hc, h.2⟩

theorem Safe.ok (hc : c ≤ k) (h : V c τ v) : Safe (.ok v, c) k τ R :=
  ⟨hc, .inr (.inl ⟨v, rfl, h⟩)⟩

theorem Safe.not_stuck (h : Safe p k τ R) : p.1 ≠ .stuck s := by
  rcases h.2 with h | ⟨_, h, _⟩ | ⟨_, h⟩ | ⟨_, h, _⟩ <;> rw [h] <;> simp

/-- A call's outcome is safe at its result type, in any function. -/
theorem Lands.safe (h : Lands p k (fun c v => V c τ v) (fun _ _ => False)) : Safe p k τ R := by
  rcases h with ⟨hc, h | h | h | ⟨_, _, h⟩⟩
  · exact ⟨hc, .inl h⟩
  · exact ⟨hc, .inr (.inl h)⟩
  · exact ⟨hc, .inr (.inr (.inl h))⟩
  · exact h.elim

/-- Continuing a safe outcome with a safe continuation is safe. -/
theorem Safe.bindC {K : Value → Nat → Result × Nat} (h : Safe p k τ₁ R)
    (hK : ∀ v, p.1 = .ok v → V p.2 τ₁ v → Safe (K v p.2) p.2 τ R) : Safe (Inty.bindC p K) k τ R := by
  obtain ⟨r, c⟩ := p
  obtain ⟨hc, h⟩ := h
  rcases h with h | ⟨v, h, hv⟩ | ⟨v, h⟩ | ⟨v, h, hv⟩ <;> simp only at h <;> subst h
  · exact ⟨hc, .inl rfl⟩
  · exact (hK v rfl hv).weaken hc
  · exact ⟨hc, .inr (.inr (.inl ⟨v, rfl⟩))⟩
  · exact ⟨hc, .inr (.inr (.inr ⟨v, rfl, hv⟩))⟩

/-- A call's body returns its function's result type, by `return` or as its
value. -/
theorem Safe.catchReturn (h : Safe p k τ (some τ)) :
    Lands (p.1.catchReturn, p.2) k (fun c v => V c τ v) (fun _ _ => False) := by
  obtain ⟨r, c⟩ := p
  obtain ⟨hc, h⟩ := h
  rcases h with h | ⟨v, h, hv⟩ | ⟨v, h⟩ | ⟨v, h, τr, hR, hv⟩ <;> simp only at h <;> subst h
  · exact ⟨hc, .inl rfl⟩
  · exact ⟨hc, .inr (.inl ⟨v, rfl, hv⟩)⟩
  · exact ⟨hc, .inr (.inr (.inl ⟨v, rfl⟩))⟩
  · cases hR; exact ⟨hc, .inr (.inl ⟨v, rfl, hv⟩)⟩

/-! ## Environments -/

/-- A value has every instance of the scheme whose constraints hold. -/
def SchemeV (k : Nat) (s : Scheme) (v : Value) : Prop :=
  ∀ τs, τs.length = s.arity → Holds (s.instPreds τs) → V k (s.inst τs) v

theorem SchemeV.mono_iff {k : Nat} {τ : Ty} {v : Value} :
    SchemeV k (.mono τ) v ↔ V k τ v :=
  ⟨fun h => by simpa using h [] rfl (by simp [Holds, Scheme.instPreds, Scheme.mono]),
    fun h _ _ _ => by simpa using h⟩

/-- `G k Γ env`: each value in `env` has the scheme `Γ` gives its variable. -/
def G (k : Nat) : Ctx → Env → Prop
  | [], [] => True
  | s :: Γ, v :: env => SchemeV k s v ∧ G k Γ env
  | _, _ => False

theorem G.mono {j k : Nat} (h : j ≤ k) : ∀ {Γ : Ctx} {env : Env}, G k Γ env → G j Γ env
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hv, hG⟩ => ⟨fun τs hl hp => V.mono h (hv τs hl hp), G.mono h hG⟩

theorem G.lookup : ∀ {i : Nat} {Γ : Ctx} {env : Env} {s : Scheme}, G k Γ env →
    Γ[i]? = some s → ∃ v, env[i]? = some v ∧ SchemeV k s v
  | _, [], _, _, _, hi => by simp at hi
  | 0, _ :: _, _ :: _, _, ⟨hv, _⟩, hi => by simp at hi; subst hi; exact ⟨_, rfl, hv⟩
  | i + 1, _ :: _, _ :: _, _, ⟨_, hG⟩, hi => by simpa using G.lookup hG (by simpa using hi)

/-! ## Operators -/

theorem Lit.eval_sound (h : LitTy l τ) : V k τ l.eval := by
  cases h
  all_goals first | exact ⟨_, rfl⟩ | rfl

theorem UnOp.eval_sound (hop : UnOpTy op τ₁ τ) (hv : V c τ₁ v) (hc : c ≤ k) :
    Safe (op.eval v, c) k τ R := by
  cases hop with
  | not => exact Safe.ok hc ⟨_, rfl⟩
  | typeof => exact Safe.ok hc ⟨_, rfl⟩
  | neg => obtain ⟨n, rfl⟩ := hv; exact Safe.ok hc ⟨_, rfl⟩

theorem BinOp.eval_sound (hC : Holds C) (hop : BinOpTy C op τ₁ τ₂ τ)
    (hv₁ : V c τ₁ v₁) (hv₂ : V c τ₂ v₂) (hc : c ≤ k) : Safe (op.eval v₁ v₂, c) k τ R := by
  cases hop with
  | plus hp =>
    cases hp.holds hC with
    | plusNumber =>
      obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂; exact Safe.ok hc ⟨_, rfl⟩
    | plusString =>
      obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂; exact Safe.ok hc ⟨_, rfl⟩
  | minus => obtain ⟨_, rfl⟩ := hv₁; obtain ⟨_, rfl⟩ := hv₂; exact Safe.ok hc ⟨_, rfl⟩

/-- Running a syntactic value gives a value, and takes no clock. -/
theorem IsValue.run_value (hv : e.IsValue) (ht : HasType C Γ R e τ) (henv : G k Γ env) :
    ∃ v, run k env e = (.ok v, k) := by
  cases hv with
  | lit => rename_i l; exact ⟨l.eval, by simp [run]⟩
  | func => rename_i body; exact ⟨.closure env body, by simp [run]⟩
  | var =>
    cases ht with
    | var hi _ _ =>
      obtain ⟨v, hv, _⟩ := G.lookup henv hi
      exact ⟨v, by simp [run, hv]⟩

/-- `Safe.bindC` for a `const`'s initialiser, safe at every instance of its
scheme whose constraints hold. Either some instance's constraints hold, or
the initialiser is a syntactic value, which can't complete abruptly. -/
theorem Safe.bindC_forall {p : Result × Nat} {s : Scheme} {K : Value → Nat → Result × Nat}
    (hw : (∃ τs, τs.length = s.arity ∧ Holds (s.instPreds τs)) ∨ ∃ v, p.1 = .ok v)
    (hle : p.2 ≤ k)
    (h : ∀ τs, τs.length = s.arity → Holds (s.instPreds τs) → Safe p k (s.inst τs) R)
    (hK : ∀ v, p.1 = .ok v → SchemeV p.2 s v → Safe (K v p.2) p.2 τ R) :
    Safe (Inty.bindC p K) k τ R := by
  obtain ⟨r, c⟩ := p
  cases r with
  | ok v =>
    refine (hK v rfl fun τs hl hp => ?_).weaken hle
    rcases (h τs hl hp).2 with h | ⟨_, h, hv⟩ | ⟨_, h⟩ | ⟨_, h, _⟩ <;> cases h
    exact hv
  | timeout => exact ⟨hle, .inl rfl⟩
  | thrown v => exact ⟨hle, .inr (.inr (.inl ⟨v, rfl⟩))⟩
  | stuck st =>
    rcases hw with ⟨τs, hl, hp⟩ | ⟨_, h⟩
    · exact absurd rfl (Safe.not_stuck (h τs hl hp))
    · cases h
  | returned v =>
    rcases hw with ⟨τs, hl, hp⟩ | ⟨_, h⟩
    · rcases (h τs hl hp).2 with h | ⟨_, h, _⟩ | ⟨_, h⟩ | ⟨_, h, hv⟩ <;> cases h
      exact ⟨hle, .inr (.inr (.inr ⟨v, rfl, hv⟩))⟩
    · cases h

/-! ## The fundamental lemma -/

/-- Type soundness: a well-typed expression, run with any clock in an
environment of the right types, is safe. By induction on the expression;
the typing rule for `const` types its initialiser at each instance by a
derivation that isn't a subderivation. -/
theorem run_sound (e : Expr) :
    ∀ {k C Γ R env τ}, HasType C Γ R e τ → Holds C → G k Γ env →
      Safe (run k env e) k τ R := by
  induction e with
  | lit l =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | lit hl => simp only [run]; exact Safe.ok (Nat.le_refl k) (Lit.eval_sound hl)
  | var i =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | var hi hlen hc =>
      obtain ⟨v, hv, hvt⟩ := G.lookup henv hi
      simp only [run, hv]
      exact Safe.ok (Nat.le_refl k) (hvt _ hlen (fun c h => (hc c h).holds hC))
  | func body ih =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | @func _ τ₁ τ₂ _ _ _ hb =>
      -- The closure is good for `j` calls, by induction on `j`: a call
      -- with `i + 1` to spare runs the body with `i`, where the closure
      -- itself (the function's own name) need only be good for `i`.
      have hclo : ∀ j, j ≤ k → V j (.arrow τ₁ τ₂) (.closure env body) := by
        intro j
        induction j with
        | zero =>
          intro _ i hi a _
          obtain rfl : i = 0 := by omega
          exact ⟨Nat.le_refl 0, .inl rfl⟩
        | succ j ihj =>
          intro hj i hi a ha
          cases i with
          | zero => exact ⟨Nat.le_refl 0, .inl rfl⟩
          | succ i =>
            have hG : G i (.mono τ₁ :: .mono (.arrow τ₁ τ₂) :: Γ)
                (a :: .closure env body :: env) :=
              ⟨SchemeV.mono_iff.mpr (V.mono (by omega) ha),
                SchemeV.mono_iff.mpr (V.mono (by omega) (ihj (by omega))),
                G.mono (by omega) henv⟩
            simp only [call]
            exact (Safe.catchReturn (ih hb hC hG)).weaken (by omega)
      simp only [run]
      exact Safe.ok (Nat.le_refl k) (hclo k (Nat.le_refl k))
  | app f a ihf iha =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | app hf ha =>
      rw [run_app]
      refine Safe.bindC (ihf hf hC henv) fun vf _ hvf => ?_
      have hc₁ := run_clock_le k env f
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (iha ha hC (G.mono hc₁ henv)) fun va _ hva => ?_
      have hc₂ := run_clock_le (run k env f).2 env a
      rw [Nat.min_eq_left (Nat.le_trans hc₂ hc₁)]
      exact Lands.safe (V.mono hc₂ hvf _ (Nat.le_refl _) va hva)
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | let_ s L hgen hval h₂ =>
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (L ++ ctxFtv Γ ++ s.ftv ++ C.flatMap Pred.ftv ++
        (R.map Ty.ftv).getD [])
      have hm : ∀ a, a ∈ L ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv ∨ a ∈ C.flatMap Pred.ftv ∨
          a ∈ (R.map Ty.ftv).getD [] → a < m :=
        fun a ha => lt_maxPlusOne a (by rcases ha with h | h | h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity →
          HasType (C ++ s.instPreds τs) Γ R e₁ (s.inst τs) := by
        intro τs hlen
        have h := (hgen m (fun a ha => hm a (.inl ha))).subst (Subst.block m τs)
        have hfresh : ∀ a, a < m → (Subst.block m τs).find a = none := fun a ha =>
          Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
        have hCσ : C.map (·.subst (Subst.block m τs)) = C := by
          conv => rhs; rw [← List.map_id C]
          exact List.map_congr_left (fun c hc => Pred.subst_id (fun a ha =>
            hfresh a (hm a (.inr (.inr (.inr (.inl (List.mem_flatMap.mpr ⟨c, hc, ha⟩))))))))
        have hRσ : R.map (·.subst (Subst.block m τs)) = R := by
          cases R with
          | none => rfl
          | some τr =>
            simp only [Option.map_some, Option.some.injEq]
            exact Ty.subst_id (fun a ha =>
              hfresh a (hm a (.inr (.inr (.inr (.inr (by simpa using ha)))))))
        rwa [List.map_append, hCσ, hRσ,
          Scheme.openPreds_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen,
          ctx_subst_id (fun a ha => hfresh a (hm a (.inr (.inl ha)))),
          Scheme.open_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen] at h
      have hsafe : ∀ τs, τs.length = s.arity → Holds (s.instPreds τs) →
          Safe (run k env e₁) k (s.inst τs) R := fun τs hlen hp =>
        ih₁ (hinst τs hlen) (hC.append hp) henv
      have hw : (∃ τs, τs.length = s.arity ∧ Holds (s.instPreds τs)) ∨
          ∃ v, (run k env e₁).1 = .ok v := by
        rcases hval with ⟨ha, hp⟩ | hv
        · exact .inl ⟨[], by simp [ha], by simp [Holds, Scheme.instPreds, hp]⟩
        · obtain ⟨v, hv⟩ := IsValue.run_value hv (hgen m (fun a ha => hm a (.inl ha))) henv
          exact .inr ⟨v, by rw [hv]⟩
      have hc₁ := run_clock_le k env e₁
      simp only [run]
      refine Safe.bindC_forall hw hc₁ hsafe fun v _ hv => ?_
      rw [Nat.min_eq_left hc₁]
      exact ih₂ h₂ hC ⟨hv, G.mono hc₁ henv⟩
  | cond c t e ihc iht ihe =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | cond hc htt hte =>
      simp only [run]
      refine Safe.bindC (ihc hc hC henv) fun v _ _ => ?_
      have hc₁ := run_clock_le k env c
      rw [Nat.min_eq_left hc₁]
      split
      · exact iht htt hC (G.mono hc₁ henv)
      · exact ihe hte hC (G.mono hc₁ henv)
  | unop op e ih =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | unop hop he =>
      simp only [run]
      exact Safe.bindC (ih he hC henv) fun v _ hv => UnOp.eval_sound hop hv (Nat.le_refl _)
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | binop hop h₁ h₂ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC henv) fun v₁ _ hv₁ => ?_
      have hc₁ := run_clock_le k env e₁
      rw [Nat.min_eq_left hc₁]
      refine Safe.bindC (ih₂ h₂ hC (G.mono hc₁ henv)) fun v₂ _ hv₂ => ?_
      exact BinOp.eval_sound hC hop (V.mono (run_clock_le _ env e₂) hv₁) hv₂ (Nat.le_refl _)
  | ret e ih =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | ret he =>
      simp only [run]
      exact Safe.bindC (ih he hC henv) fun v _ hv =>
        ⟨Nat.le_refl _, .inr (.inr (.inr ⟨v, rfl, _, rfl, hv⟩))⟩
  | throw_ e ih =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | throw_ he =>
      simp only [run]
      exact Safe.bindC (ih he hC henv) fun v _ _ => ⟨Nat.le_refl _, .inr (.inr (.inl ⟨v, rfl⟩))⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro k C Γ R env τ ht hC henv
    cases ht with
    | seq h₁ h₂ =>
      simp only [run]
      refine Safe.bindC (ih₁ h₁ hC henv) fun _ _ _ => ?_
      have hc₁ := run_clock_le k env e₁
      rw [Nat.min_eq_left hc₁]
      exact ih₂ h₂ hC (G.mono hc₁ henv)

/-- Type soundness, for `eval`: a value of the type, a `return` of a value
of the return type, a `throw`, or out of clock; never stuck. -/
theorem eval_sound (clock : Nat) (h : HasType C Γ R e τ) (hC : Holds C)
    (henv : G clock Γ env) : Safe (run clock env e) clock τ R :=
  run_sound e h hC henv

/-- A closed program, well typed with no assumptions and outside any
function, never gets stuck, whatever the clock. -/
theorem never_stuck (h : HasType [] [] none e τ) (clock : Nat) (s : Stuck) :
    eval clock [] e ≠ .stuck s :=
  Safe.not_stuck (run_sound e h (fun _ h => by cases h) (by simp [G]))

end Inty
