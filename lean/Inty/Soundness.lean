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
      HasType C (.mono τ₁ :: .mono (.arrow τ₁ τ₂) :: Γ) body τ₂ →
      ValTy (.closure env body) (.arrow τ₁ τ₂)

/-- `EnvTy env Γ`: each value in `env` has every instance of the scheme `Γ`
gives its variable whose constraints hold. -/
inductive EnvTy : Env → Ctx → Prop where
  | nil : EnvTy [] []
  | cons : (∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → ValTy v (s.inst τs)) →
      EnvTy env Γ → EnvTy (v :: env) (s :: Γ)
end

/-- A result is safe at `τ` when it is a value of type `τ`, or ran out of
fuel. It is never `stuck`. -/
def Safe (r : Result) (τ : Ty) : Prop :=
  r = .timeout ∨ ∃ v, r = .ok v ∧ ValTy v τ

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
    Safe (op.eval v) τ := by
  right
  cases hop with
  | not => exact ⟨_, rfl, .boolean⟩
  | typeof => exact ⟨_, rfl, .string⟩
  | neg => cases hv; exact ⟨_, rfl, .number⟩

theorem BinOp.eval_sound (hC : Holds C) (hop : BinOpTy C op τ₁ τ₂ τ)
    (hv₁ : ValTy v₁ τ₁) (hv₂ : ValTy v₂ τ₂) : Safe (op.eval v₁ v₂) τ := by
  right
  cases hop with
  | plus hc =>
    cases hc.holds hC with
    | number => cases hv₁; cases hv₂; exact ⟨_, rfl, .number⟩
    | string => cases hv₁; cases hv₂; exact ⟨_, rfl, .string⟩
  | minus => cases hv₁; cases hv₂; exact ⟨_, rfl, .number⟩

/-- Evaluating a syntactic value never gets stuck. -/
theorem IsValue.not_stuck (hv : e.IsValue) (ht : HasType C Γ e τ) (henv : EnvTy env Γ)
    (fuel : Nat) (s : Stuck) : eval fuel env e ≠ .stuck s := by
  cases fuel with
  | zero => simp [eval]
  | succ fuel =>
    cases hv with
    | lit => simp [eval]
    | func => simp [eval]
    | var =>
      cases ht with
      | var hi _ _ =>
        obtain ⟨v, hv, _⟩ := EnvTy.lookup henv hi
        simp [eval, hv]

/-- A result that isn't stuck, and is safe at every instance of a scheme
whose constraints hold, is one value with all those types, or a timeout. -/
theorem Safe.forall {r : Result} {s : Scheme} (hns : ∀ st, r ≠ .stuck st)
    (h : ∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → Safe r (s.inst τs)) :
    r = .timeout ∨ ∃ v, r = .ok v ∧
      ∀ τs, τs.length = s.arity → Holds (s.instPlus τs) → ValTy v (s.inst τs) := by
  cases r with
  | timeout => exact .inl rfl
  | stuck st => exact absurd rfl (hns st)
  | ok v =>
    refine .inr ⟨v, rfl, fun τs hlen hp => ?_⟩
    rcases h τs hlen hp with h | ⟨_, h, hv⟩
    · cases h
    · cases h; exact hv

/-- Type soundness. -/
theorem eval_sound (fuel : Nat) :
    ∀ {C Γ env e τ}, HasType C Γ e τ → Holds C → EnvTy env Γ →
      Safe (eval fuel env e) τ := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _; exact .inl rfl
  | succ fuel ih =>
    intro C Γ env e τ ht hC henv
    cases ht with
    | lit hl => exact .inr ⟨_, rfl, Lit.eval_sound hl⟩
    | var hi hlen hc =>
      obtain ⟨v, hv, hvt⟩ := EnvTy.lookup henv hi
      exact .inr ⟨v, by simp [eval, hv], hvt _ hlen (fun c h => (hc c h).holds hC)⟩
    | func hb => exact .inr ⟨_, rfl, .closure hC henv hb⟩
    | app hf ha =>
      rcases ih hf hC henv with hr | ⟨vf, hr, hvf⟩
      · exact .inl (by simp [eval, hr])
      rcases ih ha hC henv with hr' | ⟨va, hr', hva⟩
      · exact .inl (by simp [eval, hr, hr'])
      cases hvf with
      | closure hC' hcenv hbody =>
        have := ih hbody hC' (.cons (fun _ _ _ => by simpa using hva)
          (.cons (fun _ _ _ => by simpa using ValTy.closure hC' hcenv hbody) hcenv))
        simpa [Safe, eval, hr, hr'] using this
    | let_ s L hgen hval h₂ =>
      rename_i e₁ e₂
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (L ++ ctxFtv Γ ++ s.ftv ++ C.flatMap Ty.ftv)
      have hm : ∀ a, a ∈ L ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv ∨ a ∈ C.flatMap Ty.ftv → a < m :=
        fun a ha => lt_maxPlusOne a (by rcases ha with h | h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity →
          HasType (C ++ s.instPlus τs) Γ e₁ (s.inst τs) := by
        intro τs hlen
        have h := (hgen m (fun a ha => hm a (.inl ha))).subst (Subst.block m τs)
        have hfresh : ∀ a, a < m → (Subst.block m τs).find a = none := fun a ha =>
          Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
        have hCσ : C.map (·.subst (Subst.block m τs)) = C := by
          conv => rhs; rw [← List.map_id C]
          exact List.map_congr_left (fun c hc => Ty.subst_id (fun a ha =>
            hfresh a (hm a (.inr (.inr (.inr (List.mem_flatMap.mpr ⟨c, hc, ha⟩)))))))
        rwa [List.map_append, hCσ,
          Scheme.openPlus_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen,
          ctx_subst_id (fun a ha => hfresh a (hm a (.inr (.inl ha)))),
          Scheme.open_block s (fun a ha => hm a (.inr (.inr (.inl ha)))) hlen] at h
      have hsafe : ∀ τs, τs.length = s.arity → Holds (s.instPlus τs) →
          Safe (eval fuel env e₁) (s.inst τs) := fun τs hlen hp =>
        ih (hinst τs hlen) (hC.append hp) henv
      have hns : ∀ st, eval fuel env e₁ ≠ .stuck st := by
        rcases hval with ⟨ha, hp⟩ | hv
        · intro st hst
          rcases hsafe [] (by simp [ha]) (by simp [Holds, Scheme.instPlus, hp])
            with h | ⟨_, h, _⟩ <;> rw [hst] at h <;> cases h
        · exact IsValue.not_stuck hv (hgen m (fun a ha => hm a (.inl ha))) henv fuel
      rcases Safe.forall hns hsafe with hr | ⟨v, hr, hv⟩
      · exact .inl (by simp [eval, hr])
      simpa [Safe, eval, hr] using ih h₂ hC (.cons hv henv)
    | cond hc htt hte =>
      rcases ih hc hC henv with hr | ⟨v, hr, _⟩
      · exact .inl (by simp [eval, hr])
      by_cases hb : v.truthy
      · simpa [Safe, eval, hr, hb] using ih htt hC henv
      · simpa [Safe, eval, hr, hb] using ih hte hC henv
    | unop hop he =>
      rcases ih he hC henv with hr | ⟨v, hr, hv⟩
      · exact .inl (by simp [eval, hr])
      simpa [Safe, eval, hr] using UnOp.eval_sound hop hv
    | binop hop h₁ h₂ =>
      rcases ih h₁ hC henv with hr | ⟨v₁, hr, hv₁⟩
      · exact .inl (by simp [eval, hr])
      rcases ih h₂ hC henv with hr' | ⟨v₂, hr', hv₂⟩
      · exact .inl (by simp [eval, hr, hr'])
      simpa [Safe, eval, hr, hr'] using BinOp.eval_sound hC hop hv₁ hv₂

/-- A closed program, well typed with no assumptions, never gets stuck,
whatever the fuel. -/
theorem never_stuck (h : HasType [] [] e τ) (fuel : Nat) (s : Stuck) :
    eval fuel [] e ≠ .stuck s := by
  rcases eval_sound fuel h (fun _ h => by cases h) .nil with hr | ⟨_, hr, _⟩ <;> simp [hr]

end Inty
