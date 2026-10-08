import Inty.TypeSubst
import Inty.Semantics

/-!
# Type soundness

A well-typed program never gets stuck: with any amount of fuel, `eval` either
runs out of fuel or returns a value of the expected type. This is the theorem
`src/meta/soundness.rs` tests by sampling ("Whenever inty accepts a program,
the operational semantics must not get stuck on it"), proved for every
program of the calculus.

The proof is by induction on fuel. Values are typed by a value-typing
relation, `ValTy`: a closure has type `τ₁ → τ₂` when its body is well typed
in a context its captured environment satisfies, under `Plus` assumptions
that hold.
-/

namespace Inty

/-- Every type in `C` is a `Plus` instance. -/
def Holds (C : List Ty) : Prop := ∀ c ∈ C, PlusInst c

theorem Holds.append {C D : List Ty} (hC : Holds C) (hD : Holds D) : Holds (C ++ D) :=
  fun c hc => (List.mem_append.mp hc).elim (hC c) (hD c)

theorem Entails.holds {C : List Ty} (hC : Holds C) (h : Entails C τ) : PlusInst τ :=
  h.elim id (hC τ)

mutual
/-- `ValTy v τ`: the value `v` has type `τ`. -/
inductive ValTy : Value → Ty → Prop where
  | number : ValTy (.number n) .number
  | string : ValTy (.string s) .string
  | boolean : ValTy (.boolean b) .boolean
  | undefined : ValTy .undefined .undefined
  | null : ValTy .null .null
  | closure : Holds C → EnvTy env Γ →
      HasType C (.mono τ₁ :: .mono (.arrow τ₁ τ₂) :: Γ) (some τ₂) body τ₂ →
      ValTy (.closure env body) (.arrow τ₁ τ₂)

/-- `EnvTy env Γ`: each value in `env` has every instance of the scheme `Γ`
gives its variable whose constraints hold. -/
inductive EnvTy : Env → Ctx → Prop where
  | nil : EnvTy [] []
  | cons : (∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → ValTy v (s.inst τs)) →
      EnvTy env Γ → EnvTy (v :: env) (s :: Γ)
end

/-- A result is safe at `τ`, in a function returning `R`: a value of type
`τ`, a `return` of a value of the return type, a `throw` of any value, or
out of fuel. It is never `stuck`. -/
def Safe (r : Result) (τ : Ty) (R : Option Ty) : Prop :=
  r = .timeout ∨ (∃ v, r = .ok v ∧ ValTy v τ) ∨ (∃ v, r = .thrown v) ∨
    (∃ τr v, R = some τr ∧ r = .returned v ∧ ValTy v τr)

theorem Safe.ok (h : ValTy v τ) : Safe (.ok v) τ R := .inr (.inl ⟨v, rfl, h⟩)

theorem Safe.not_stuck (h : Safe r τ R) : r ≠ .stuck s := by
  rcases h with rfl | ⟨_, rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;> simp

/-- Continuing a safe result with a safe continuation is safe. -/
theorem Safe.bind {k : Value → Result} (h : Safe r τ₁ R)
    (hk : ∀ v, ValTy v τ₁ → Safe (k v) τ R) : Safe (r.bind k) τ R := by
  rcases h with rfl | ⟨v, rfl, hv⟩ | ⟨v, rfl⟩ | ⟨τr, v, hR, rfl, hv⟩
  · exact .inl rfl
  · exact hk v hv
  · exact .inr (.inr (.inl ⟨v, rfl⟩))
  · exact .inr (.inr (.inr ⟨τr, v, hR, rfl, hv⟩))

/-- A call's body returns its function's result type, by `return` or as its
value. -/
theorem Safe.catchReturn (h : Safe r τ (some τ)) : Safe r.catchReturn τ R := by
  rcases h with rfl | ⟨v, rfl, hv⟩ | ⟨v, rfl⟩ | ⟨τr, v, hR, rfl, hv⟩
  · exact .inl rfl
  · exact Safe.ok hv
  · exact .inr (.inr (.inl ⟨v, rfl⟩))
  · cases hR; exact Safe.ok hv

-- `EnvTy` is mutually inductive, so this recurses on the index instead of
-- inducting on the environment.
theorem EnvTy.lookup :
    ∀ {i : Nat} {env : Env} {Γ : Ctx} {s}, EnvTy env Γ → Γ[i]? = some s →
      ∃ v, env[i]? = some v ∧
        ∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → ValTy v (s.inst τs)
  | _, _, _, _, .nil, hi => by simp at hi
  | 0, _, _, _, .cons hv _, hi => by simp at hi; subst hi; exact ⟨_, rfl, hv⟩
  | i + 1, _, _, _, .cons _ h, hi => by simpa using EnvTy.lookup h (by simpa using hi)

theorem Lit.eval_sound (h : LitTy l τ) : ValTy l.eval τ := by
  cases h <;> constructor

theorem UnOp.eval_sound (hop : UnOpTy op τ₁ τ) (hv : ValTy v τ₁) :
    Safe (op.eval v) τ R := by
  cases hop with
  | not => exact Safe.ok .boolean
  | typeof => exact Safe.ok .string
  | neg => cases hv; exact Safe.ok .number

theorem BinOp.eval_sound (hC : Holds C) (hop : BinOpTy C op τ₁ τ₂ τ)
    (hv₁ : ValTy v₁ τ₁) (hv₂ : ValTy v₂ τ₂) : Safe (op.eval v₁ v₂) τ R := by
  cases hop with
  | plus hc =>
    cases hc.holds hC with
    | number => cases hv₁; cases hv₂; exact Safe.ok .number
    | string => cases hv₁; cases hv₂; exact Safe.ok .string
  | minus => cases hv₁; cases hv₂; exact Safe.ok .number

/-- Evaluating a syntactic value only runs out of fuel or gives a value. -/
theorem IsValue.eval_value (hv : e.IsValue) (ht : HasType C Γ R e τ) (henv : EnvTy env Γ)
    (fuel : Nat) : eval fuel env e = .timeout ∨ ∃ v, eval fuel env e = .ok v := by
  cases fuel with
  | zero => exact .inl rfl
  | succ fuel =>
    cases hv with
    | lit => exact .inr ⟨_, rfl⟩
    | func => exact .inr ⟨_, rfl⟩
    | var =>
      cases ht with
      | var hi _ _ =>
        obtain ⟨v, hv, _⟩ := EnvTy.lookup henv hi
        exact .inr ⟨v, by simp only [eval, hv]⟩

/-- `Safe.bind` for a `const`'s initialiser, safe at every instance of its
scheme whose constraints hold. Either some instance's constraints hold, or
the initialiser is a syntactic value, which can't complete abruptly. -/
theorem Safe.bind_forall {r : Result} {s : Scheme} {k : Value → Result}
    (hw : (∃ τs, τs.length = s.arity ∧ Holds (s.instPlus τs)) ∨
      (r = .timeout ∨ ∃ v, r = .ok v))
    (h : ∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → Safe r (s.inst τs) R)
    (hk : ∀ v, (∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → ValTy v (s.inst τs)) →
      Safe (k v) τ R) : Safe (r.bind k) τ R := by
  cases r with
  | ok v =>
    refine hk v (fun τs hl hp => ?_)
    rcases h τs hl hp with h | ⟨_, h, hv⟩ | ⟨_, h⟩ | ⟨_, _, _, h, _⟩ <;> cases h
    exact hv
  | timeout => exact .inl rfl
  | thrown v => exact .inr (.inr (.inl ⟨v, rfl⟩))
  | stuck st =>
    rcases hw with ⟨τs, hl, hp⟩ | hw
    · exact absurd (h τs hl hp) (fun hs => Safe.not_stuck hs rfl)
    · rcases hw with h | ⟨_, h⟩ <;> cases h
  | returned v =>
    rcases hw with ⟨τs, hl, hp⟩ | hw
    · rcases h τs hl hp with h | ⟨_, h, _⟩ | ⟨_, h⟩ | ⟨τr, _, hR, h, hv⟩ <;> cases h
      exact .inr (.inr (.inr ⟨τr, v, hR, rfl, hv⟩))
    · rcases hw with h | ⟨_, h⟩ <;> cases h

/-- Type soundness. -/
theorem eval_sound (fuel : Nat) :
    ∀ {C Γ R env e τ}, HasType C Γ R e τ → Holds C → EnvTy env Γ →
      Safe (eval fuel env e) τ R := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _; exact .inl rfl
  | succ fuel ih =>
    intro C Γ R env e τ ht hC henv
    cases ht with
    | lit hl => exact Safe.ok (Lit.eval_sound hl)
    | var hi hlen hc =>
      obtain ⟨v, hv, hvt⟩ := EnvTy.lookup henv hi
      simp only [eval, hv]
      exact Safe.ok (hvt _ hlen (fun c h => (hc c h).holds hC))
    | func hb => exact Safe.ok (.closure hC henv hb)
    | app hf ha =>
      simp only [eval]
      refine Safe.bind (ih hf hC henv) fun vf hvf => Safe.bind (ih ha hC henv) fun va hva => ?_
      cases hvf with
      | closure hC' hcenv hbody =>
        exact Safe.catchReturn (ih hbody hC' (.cons (fun _ _ _ => by simpa using hva)
          (.cons (fun _ _ _ => by simpa using ValTy.closure hC' hcenv hbody) hcenv)))
    | let_ s L hgen hval h₂ =>
      rename_i e₁ e₂
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (L ++ ctxFtv Γ ++ s.ftv ++ C.flatMap Ty.ftv ++
        (R.map Ty.ftv).getD [])
      have hm : ∀ a, a ∈ L ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv ∨ a ∈ C.flatMap Ty.ftv ∨
          a ∈ (R.map Ty.ftv).getD [] → a < m :=
        fun a ha => lt_maxPlusOne a (by rcases ha with h | h | h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity →
          HasType (C ++ s.instPlus τs) Γ R e₁ (s.inst τs) := by
        intro τs hlen
        have h := (hgen m (fun a ha => hm a (.inl ha))).subst (Subst.block m τs)
        have hfresh : ∀ a, a < m → (Subst.block m τs).find a = none := fun a ha =>
          Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
        have hCσ : C.map (·.subst (Subst.block m τs)) = C := by
          conv => rhs; rw [← List.map_id C]
          exact List.map_congr_left (fun c hc => Ty.subst_id (fun a ha =>
            hfresh a (hm a (.inr (.inr (.inr (.inl (List.mem_flatMap.mpr ⟨c, hc, ha⟩))))))))
        have hRσ : R.map (·.subst (Subst.block m τs)) = R := by
          cases R with
          | none => rfl
          | some τr =>
            simp only [Option.map_some, Option.some.injEq]
            exact Ty.subst_id (fun a ha =>
              hfresh a (hm a (.inr (.inr (.inr (.inr (by simpa using ha)))))))
        rwa [List.map_append, hCσ, hRσ,
          Scheme.openPlus_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen,
          ctx_subst_id (fun a ha => hfresh a (hm a (.inr (.inl ha)))),
          Scheme.open_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen] at h
      have hsafe : ∀ τs, τs.length = s.arity → Holds (s.instPlus τs) →
          Safe (eval fuel env e₁) (s.inst τs) R := fun τs hlen hp =>
        ih (hinst τs hlen) (hC.append hp) henv
      have hw : (∃ τs, τs.length = s.arity ∧ Holds (s.instPlus τs)) ∨
          (eval fuel env e₁ = .timeout ∨ ∃ v, eval fuel env e₁ = .ok v) := by
        rcases hval with ⟨ha, hp⟩ | hv
        · exact .inl ⟨[], by simp [ha], by simp [Holds, Scheme.instPlus, hp]⟩
        · exact .inr (IsValue.eval_value hv (hgen m (fun a ha => hm a (.inl ha))) henv fuel)
      simp only [eval]
      exact Safe.bind_forall hw hsafe fun v hv => ih h₂ hC (.cons hv henv)
    | cond hc htt hte =>
      simp only [eval]
      refine Safe.bind (ih hc hC henv) fun v _ => ?_
      split
      · exact ih htt hC henv
      · exact ih hte hC henv
    | unop hop he =>
      simp only [eval]
      exact Safe.bind (ih he hC henv) fun v hv => UnOp.eval_sound hop hv
    | binop hop h₁ h₂ =>
      simp only [eval]
      exact Safe.bind (ih h₁ hC henv) fun v₁ hv₁ =>
        Safe.bind (ih h₂ hC henv) fun v₂ hv₂ => BinOp.eval_sound hC hop hv₁ hv₂
    | ret he =>
      simp only [eval]
      exact Safe.bind (ih he hC henv) fun v hv => .inr (.inr (.inr ⟨_, v, rfl, rfl, hv⟩))
    | throw_ he =>
      simp only [eval]
      exact Safe.bind (ih he hC henv) fun v _ => .inr (.inr (.inl ⟨v, rfl⟩))
    | seq h₁ h₂ =>
      simp only [eval]
      exact Safe.bind (ih h₁ hC henv) fun _ _ => ih h₂ hC henv

/-- A closed program, well typed with no assumptions and outside any
function, never gets stuck, whatever the fuel. -/
theorem never_stuck (h : HasType [] [] none e τ) (fuel : Nat) (s : Stuck) :
    eval fuel [] e ≠ .stuck s :=
  Safe.not_stuck (eval_sound fuel h (fun _ h => by cases h) .nil)

end Inty
