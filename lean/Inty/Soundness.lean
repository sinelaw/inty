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
in a context its captured environment satisfies.
-/

namespace Inty

mutual
/-- `ValTy v τ`: the value `v` has type `τ`. -/
inductive ValTy : Value → Ty → Prop where
  | number : ValTy (.number n) .number
  | string : ValTy (.string s) .string
  | boolean : ValTy (.boolean b) .boolean
  | undefined : ValTy .undefined .undefined
  | null : ValTy .null .null
  | closure : EnvTy env Γ →
      HasType (.mono τ₁ :: .mono (.arrow τ₁ τ₂) :: Γ) body τ₂ →
      ValTy (.closure env body) (.arrow τ₁ τ₂)

/-- `EnvTy env Γ`: each value in `env` has every instance of the scheme `Γ`
gives its variable. -/
inductive EnvTy : Env → Ctx → Prop where
  | nil : EnvTy [] []
  | cons : (∀ τs, τs.length = s.arity → ValTy v (s.inst τs)) → EnvTy env Γ →
      EnvTy (v :: env) (s :: Γ)
end

/-- A result is safe at `τ` when it is a value of type `τ`, or ran out of
fuel. It is never `stuck`. -/
def Safe (r : Result) (τ : Ty) : Prop :=
  r = .timeout ∨ ∃ v, r = .ok v ∧ ValTy v τ

-- `EnvTy` is mutually inductive, so this recurses on the index instead of
-- inducting on the environment.
theorem EnvTy.lookup :
    ∀ {i : Nat} {env : Env} {Γ : Ctx} {s}, EnvTy env Γ → Γ[i]? = some s →
      ∃ v, env[i]? = some v ∧ ∀ τs, τs.length = s.arity → ValTy v (s.inst τs)
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

theorem BinOp.eval_sound (hop : BinOpTy op τ₁ τ₂ τ) (hv₁ : ValTy v₁ τ₁)
    (hv₂ : ValTy v₂ τ₂) : Safe (op.eval v₁ v₂) τ := by
  right
  cases hop with
  | plus hc =>
    cases hc with
    | number => cases hv₁; cases hv₂; exact ⟨_, rfl, .number⟩
    | string => cases hv₁; cases hv₂; exact ⟨_, rfl, .string⟩
  | minus => cases hv₁; cases hv₂; exact ⟨_, rfl, .number⟩

/-- A result safe at every instance of a scheme is one value with all those
types, or a timeout. -/
theorem Safe.forall {r : Result} {s : Scheme}
    (h : ∀ τs, τs.length = s.arity → Safe r (s.inst τs)) :
    r = .timeout ∨ ∃ v, r = .ok v ∧ ∀ τs, τs.length = s.arity → ValTy v (s.inst τs) := by
  cases r with
  | timeout => exact .inl rfl
  | stuck _ =>
    rcases h (List.replicate s.arity .undefined) (by simp) with h | ⟨_, h, _⟩ <;> cases h
  | ok v =>
    refine .inr ⟨v, rfl, fun τs hlen => ?_⟩
    rcases h τs hlen with h | ⟨_, h, hv⟩
    · cases h
    · cases h; exact hv

/-- Type soundness. -/
theorem eval_sound (fuel : Nat) :
    ∀ {Γ env e τ}, HasType Γ e τ → EnvTy env Γ → Safe (eval fuel env e) τ := by
  induction fuel with
  | zero => intro _ _ _ _ _ _; exact .inl rfl
  | succ fuel ih =>
    intro Γ env e τ ht henv
    cases ht with
    | lit hl => exact .inr ⟨_, rfl, Lit.eval_sound hl⟩
    | var hi hlen =>
      obtain ⟨v, hv, hvt⟩ := EnvTy.lookup henv hi
      exact .inr ⟨v, by simp [eval, hv], hvt _ hlen⟩
    | func hb => exact .inr ⟨_, rfl, .closure henv hb⟩
    | app hf ha =>
      rcases ih hf henv with hr | ⟨vf, hr, hvf⟩
      · exact .inl (by simp [eval, hr])
      rcases ih ha henv with hr' | ⟨va, hr', hva⟩
      · exact .inl (by simp [eval, hr, hr'])
      cases hvf with
      | closure hcenv hbody =>
        have := ih hbody (.cons (fun _ _ => by simpa using hva)
          (.cons (fun _ _ => by simpa using ValTy.closure hcenv hbody) hcenv))
        simpa [Safe, eval, hr, hr'] using this
    | let_ s L hgen _hv h₂ =>
      rename_i e₁ e₂
      -- Type `e₁` at each instance of `s`: open `s` at variables above
      -- everything in sight, then substitute the instance's types for them.
      let m := maxPlusOne (L ++ ctxFtv Γ ++ s.ftv)
      have hm : ∀ a, a ∈ L ∨ a ∈ ctxFtv Γ ∨ a ∈ s.ftv → a < m := fun a ha =>
        lt_maxPlusOne a (by rcases ha with h | h | h <;> simp [h])
      have hinst : ∀ τs, τs.length = s.arity → HasType Γ e₁ (s.inst τs) := by
        intro τs hlen
        have h := (hgen m (fun a ha => hm a (.inl ha))).subst (Subst.block m τs)
        have hfresh : ∀ a, a < m → (Subst.block m τs).find a = none := fun a ha =>
          Subst.find_none (fun p hp e => by have := Subst.block_keys p hp; omega)
        rwa [ctx_subst_id (fun a ha => hfresh a (hm a (.inr (.inl ha)))),
          Scheme.open_block s (fun a ha => hm a (.inr (.inr ha))) hlen] at h
      rcases Safe.forall (fun τs hlen => ih (hinst τs hlen) henv) with hr | ⟨v, hr, hv⟩
      · exact .inl (by simp [eval, hr])
      simpa [Safe, eval, hr] using ih h₂ (.cons hv henv)
    | cond hc htt hte =>
      rcases ih hc henv with hr | ⟨v, hr, _⟩
      · exact .inl (by simp [eval, hr])
      by_cases hb : v.truthy
      · simpa [Safe, eval, hr, hb] using ih htt henv
      · simpa [Safe, eval, hr, hb] using ih hte henv
    | unop hop he =>
      rcases ih he henv with hr | ⟨v, hr, hv⟩
      · exact .inl (by simp [eval, hr])
      simpa [Safe, eval, hr] using UnOp.eval_sound hop hv
    | binop hop h₁ h₂ =>
      rcases ih h₁ henv with hr | ⟨v₁, hr, hv₁⟩
      · exact .inl (by simp [eval, hr])
      rcases ih h₂ henv with hr' | ⟨v₂, hr', hv₂⟩
      · exact .inl (by simp [eval, hr, hr'])
      simpa [Safe, eval, hr, hr'] using BinOp.eval_sound hop hv₁ hv₂

/-- A closed, well-typed program never gets stuck, whatever the fuel. -/
theorem never_stuck (h : HasType [] e τ) (fuel : Nat) (s : Stuck) :
    eval fuel [] e ≠ .stuck s := by
  rcases eval_sound fuel h .nil with hr | ⟨_, hr, _⟩ <;> simp [hr]

end Inty
