import Inty.Infer
import Inty.Soundness

/-!
# Soundness of inference

Whatever `infer` returns is a valid typing: `inferProgram e = some τ` implies
`HasType [] e τ`. With `never_stuck` (`Inty.Soundness`), a program inference
accepts never gets stuck.
-/

namespace Inty

/-- A single binding `a ↦ τ`, with `a` not in `τ`, unifies `var a` with `τ`. -/
theorem Ty.subst_single {a : Nat} {τ : Ty} (h : a ∉ τ.ftv) : τ.subst [(a, τ)] = τ :=
  Ty.subst_id (fun b hb => by
    have : b ≠ a := fun e => h (e ▸ hb)
    simp [Subst.find, this])

theorem unify_sound :
    ∀ {fuel : Nat} {τ₁ τ₂ : Ty} {σ : Subst}, unify fuel τ₁ τ₂ = some σ →
      τ₁.subst σ = τ₂.subst σ
  | 0, _, _, _, h => by simp [unify] at h
  | fuel + 1, τ₁, τ₂, σ, h => by
    unfold unify at h
    split at h
    · split at h <;> cases h
      · subst_vars; rfl
      · rename_i hne
        have : ¬_ = _ := Ne.symm hne
        simp [Ty.subst, Subst.find, this]
    · split at h
      · cases h
      · cases h; rename_i hocc
        simp [Ty.subst, Subst.find, Ty.subst_single hocc]
    · split at h
      · cases h
      · cases h; rename_i hocc
        simp [Ty.subst, Subst.find, Ty.subst_single hocc]
    · split at h
      · cases h
      rename_i σ₁ h₁
      split at h
      · cases h
      rename_i σ₂ h₂
      cases h
      have e₁ := unify_sound h₁
      have e₂ := unify_sound h₂
      simp [e₁, e₂]
    · split at h
      · cases h; subst_vars; rfl
      · cases h

/-- `φ` makes every type in `P` an instance of `Plus`. -/
def Sat (P : List Ty) (φ : Subst) : Prop := ∀ c ∈ P, PlusInst (c.subst φ)

@[simp] theorem Sat.nil (φ : Subst) : Sat [] φ := by simp [Sat]

@[simp] theorem Sat.append {P Q : List Ty} {φ : Subst} :
    Sat (P ++ Q) φ ↔ Sat P φ ∧ Sat Q φ := by
  simp only [Sat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

@[simp] theorem Sat.map {P : List Ty} {σ φ : Subst} :
    Sat (P.map (·.subst σ)) φ ↔ Sat P (Subst.compose φ σ) := by
  simp [Sat]

@[simp] theorem Sat.singleton {τ : Ty} {φ : Subst} :
    Sat [τ] φ ↔ PlusInst (τ.subst φ) := by
  simp [Sat]

theorem Lit.ty_sound (l : Lit) : LitTy l l.ty := by cases l <;> constructor

@[simp] theorem Lit.ty_subst (l : Lit) (σ : Subst) : l.ty.subst σ = l.ty := by
  cases l <;> rfl

theorem Expr.isValue_sound {e : Expr} (h : e.isValue = true) : e.IsValue := by
  cases e <;> first | constructor | simp [Expr.isValue] at h

/-- Soundness of Algorithm W: the inferred type, under the inferred
substitution and any further substitution that resolves the `Plus`
constraints, is a valid typing. -/
theorem infer_sound :
    ∀ {e : Expr} {Γ : Ctx} {n : Nat} {o : Out}, infer Γ e n = some o →
      ∀ φ, Sat o.plus φ → HasType (Ctx.subst φ (Ctx.subst o.σ Γ)) e (o.τ.subst φ) := by
  intro e
  induction e with
  | lit l =>
    intro Γ n o h φ _
    simp only [infer, Option.some.injEq] at h; subst h
    simpa using HasType.lit (Γ := Ctx.subst φ Γ) (Lit.ty_sound l)
  | var i =>
    intro Γ n o h φ _
    simp only [infer] at h
    split at h
    · rename_i s hs
      simp only [Option.some.injEq] at h; subst h
      simp only [Ctx.subst_nil, Scheme.open, Scheme.inst_subst]
      exact .var (by rw [Ctx.getElem?_subst, hs]; rfl) (by simp)
    · cases h
  | func body ih =>
    intro Γ n o h φ hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map] at hsat
    have := ih h₁ _ hsat
    simp only [Ctx.subst_cons, Scheme.mono_subst, Ty.subst_arrow, Ty.subst_compose,
      Ctx.subst_compose] at this ⊢
    rw [← unify_sound hu] at this
    exact .func this
  | app f a ihf iha =>
    intro Γ n o h φ hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    rename_i σ₃ hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have hf := ihf h₁ _ hsat.1
    have ha := iha h₂ _ hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose] at hf ha ⊢
    rw [unify_sound hu] at hf
    exact .app hf ha
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Γ n o h φ hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he₂ := ih₂ h₂ φ hsat.2
    simp only [Ctx.subst_cons, Ctx.subst_compose] at he₂ ⊢
    refine .let_ _ [] (fun m _ => ?_) ?_ he₂
    · split
      · -- Generalised: rename the generalised variables to the block at `m`.
        rename_i hv
        let avoid := ctxFtv (Ctx.subst o₁.σ Γ) ++ o₁.plus.flatMap Ty.ftv
        let ᾱ := o₁.τ.ftv.filter (fun a => a ∉ avoid)
        have hout : ∀ a ∈ avoid, a ∉ ᾱ := fun a ha hα => by
          simp only [ᾱ, List.mem_filter, decide_eq_true_eq] at hα; exact hα.2 ha
        let ψ := renameBlock ᾱ m ++ Subst.compose φ o₂.σ
        have hψ : ∀ a ∈ avoid, ψ.find a = (Subst.compose φ o₂.σ).find a :=
          fun a ha => renameBlock_append_find m _ (hout a ha)
        have hsat₁ : Sat o₁.plus ψ := fun c hc => by
          rw [Ty.subst_congr (fun a ha => hψ a (by
            simp only [avoid, List.mem_append, List.mem_flatMap]; exact .inr ⟨c, hc, ha⟩))]
          exact hsat.1 c hc
        have := ih₁ h₁ ψ hsat₁
        rw [Ctx.subst_congr (fun a ha => hψ a (List.mem_append_left _ ha)),
          Ty.gen_open] at this
        rw [Ctx.subst_compose, Scheme.subst_compose] at this
        exact this
      · simpa using ih₁ h₁ _ hsat.1
    · split
      · rename_i hv; exact .inr (Expr.isValue_sound hv)
      · exact .inl rfl
  | cond c t e ihc iht ihe =>
    intro Γ n o h φ hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    split at h
    · cases h
    rename_i o₃ h₃
    split at h
    · cases h
    rename_i σ₄ hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have hc := ihc h₁ _ hsat.1.1
    have ht := iht h₂ _ hsat.1.2
    have he := ihe h₃ _ hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose] at hc ht he ⊢
    rw [unify_sound hu] at ht
    exact .cond hc ht he
  | unop op e ih =>
    intro Γ n o h φ hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    cases op with
    | not =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .not (ih h₁ φ hsat)
    | typeof =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .typeof (ih h₁ φ hsat)
    | neg =>
      simp only at h
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have he := ih h₁ _ hsat
      simp only [Ty.subst_compose, Ctx.subst_compose] at he ⊢
      rw [unify_sound hu] at he
      exact .unop .neg he
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ n o h φ hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    cases op with
    | plus =>
      simp only at h
      split at h
      · cases h
      rename_i σ₃ hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map, Sat.append, Sat.singleton] at hsat
      have he₁ := ih₁ h₁ _ hsat.1.1
      have he₂ := ih₂ h₂ _ hsat.1.2
      simp only [Ty.subst_compose, Ctx.subst_compose] at he₁ he₂ hsat ⊢
      rw [unify_sound hu] at he₁
      exact .binop (.plus hsat.2) he₁ he₂
    | minus =>
      simp only at h
      split at h
      · cases h
      rename_i σ₃ hu₃
      split at h
      · cases h
      rename_i σ₄ hu₄
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map, Sat.append] at hsat
      have he₁ := ih₁ h₁ _ hsat.1
      have he₂ := ih₂ h₂ _ hsat.2
      simp only [Ty.subst_compose, Ctx.subst_compose] at he₁ he₂ ⊢
      rw [unify_sound hu₃] at he₁
      rw [unify_sound hu₄] at he₂
      exact .binop .minus (by simpa using he₁) (by simpa using he₂)

/-- A program inference accepts is well typed. -/
theorem inferProgram_sound {e : Expr} {τ : Ty} (h : inferProgram e = some τ) :
    HasType [] e τ := by
  simp only [inferProgram] at h
  split at h
  · cases h
  rename_i o ho
  split at h
  · rename_i hall
    simp only [Option.some.injEq] at h; subst h
    have hsat : Sat o.plus [] := fun c hc => by
      have := List.all_eq_true.mp hall c hc
      cases c <;> simp_all [Ty.isPlusInst] <;> constructor
    simpa using infer_sound ho [] hsat
  · cases h

/-- A program inference accepts never gets stuck, whatever the fuel. -/
theorem inferProgram_never_stuck {e : Expr} {τ : Ty} (h : inferProgram e = some τ)
    (fuel : Nat) (s : Stuck) : eval fuel [] e ≠ .stuck s :=
  never_stuck (inferProgram_sound h) fuel s

end Inty
