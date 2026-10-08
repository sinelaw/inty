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

/-- Under `φ`, every type in `P` is a `Plus` instance or assumed in `C`. -/
def Sat (C : List Ty) (P : List Ty) (φ : Subst) : Prop := ∀ c ∈ P, Entails C (c.subst φ)

@[simp] theorem Sat.nil (C : List Ty) (φ : Subst) : Sat C [] φ := by simp [Sat]

@[simp] theorem Sat.append {C P Q : List Ty} {φ : Subst} :
    Sat C (P ++ Q) φ ↔ Sat C P φ ∧ Sat C Q φ := by
  simp only [Sat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

@[simp] theorem Sat.map {C P : List Ty} {σ φ : Subst} :
    Sat C (P.map (·.subst σ)) φ ↔ Sat C P (Subst.compose φ σ) := by
  simp [Sat]

@[simp] theorem Sat.singleton {C : List Ty} {τ : Ty} {φ : Subst} :
    Sat C [τ] φ ↔ Entails C (τ.subst φ) := by
  simp [Sat]

theorem Entails.weaken {C : List Ty} (D : List Ty) (h : Entails C τ) : Entails (C ++ D) τ :=
  h.elim .inl (fun h => .inr (List.mem_append_left _ h))

theorem Lit.ty_sound (l : Lit) : LitTy l l.ty := by cases l <;> constructor

@[simp] theorem Lit.ty_subst (l : Lit) (σ : Subst) : l.ty.subst σ = l.ty := by
  cases l <;> rfl

theorem Expr.isValue_sound {e : Expr} (h : e.isValue = true) : e.IsValue := by
  cases e <;> first | constructor | simp [Expr.isValue] at h

/-- Soundness of Algorithm W: the inferred type, under the inferred
substitution and any further substitution that resolves the `Plus`
constraints, is a valid typing. -/
theorem infer_sound :
    ∀ {e : Expr} {Γ : Ctx} {R : Option Ty} {n : Nat} {o : Out}, infer Γ R e n = some o →
      ∀ φ C, Sat C o.plus φ →
        HasType C (Ctx.subst φ (Ctx.subst o.σ Γ)) (Ret.subst φ (Ret.subst o.σ R)) e
          (o.τ.subst φ) := by
  intro e
  induction e with
  | lit l =>
    intro Γ R n o h φ C hsat
    simp only [infer, Option.some.injEq] at h; subst h
    simpa using HasType.lit (C := C) (Γ := Ctx.subst φ Γ) (Lit.ty_sound l)
  | var i =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · rename_i s hs
      simp only [Option.some.injEq] at h; subst h
      simp only [Ctx.subst_nil, Scheme.open, Scheme.inst_subst]
      refine .var (by rw [Ctx.getElem?_subst, hs]; rfl) (by simp [varBlock]) (fun c hc => ?_)
      rw [← Scheme.instPlus_subst] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
      exact hsat c₀ hc₀
    · cases h
  | func body ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i σ' hu
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map] at hsat
    have := ih h₁ _ C hsat
    simp only [Ctx.subst_cons, Scheme.mono_subst, Ty.subst_arrow, Ty.subst_compose,
      Ctx.subst_compose, Ret.subst_compose, Ret.subst_some] at this ⊢
    rw [← unify_sound hu] at this
    exact .func this
  | app f a ihf iha =>
    intro Γ R n o h φ C hsat
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
    have hf := ihf h₁ _ C hsat.1
    have ha := iha h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hf ha ⊢
    rw [unify_sound hu] at hf
    exact .app hf ha
  | let_ e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    generalize hls : letScheme e₁ (Ctx.subst o₁.σ Γ) (Ret.subst o₁.σ R) o₁.τ o₁.plus = ls at h
    obtain ⟨s, rest⟩ := ls
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he₂ := ih₂ h₂ φ C hsat.2
    simp only [Ctx.subst_cons, Ctx.subst_compose, Ret.subst_compose] at he₂ ⊢
    simp only [letScheme] at hls
    split at hls
    · -- Generalised: rename the generalised variables to the block at `m`.
      rename_i hv
      simp only [Prod.mk.injEq] at hls; obtain ⟨rfl, rfl⟩ := hls
      refine .let_ _ [] (fun m _ => ?_) (.inr (Expr.isValue_sound hv)) he₂
      let Γ₁ := Ctx.subst o₁.σ Γ
      let R₁ := Ret.subst o₁.σ R
      let ᾱ := (o₁.τ.ftv.filter (fun a => a ∉ ctxFtv Γ₁ ++ Ret.ftv R₁)).eraseDups
      let φ₀ := Subst.compose φ o₂.σ
      let ψ := renameBlock ᾱ m ++ φ₀
      have hout : ∀ a, a ∈ ctxFtv Γ₁ ++ Ret.ftv R₁ → a ∉ ᾱ := fun a ha hα => by
        simp only [ᾱ, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at hα
        exact hα.2 ha
      have hΓ : Ctx.subst ψ Γ₁ = Ctx.subst φ₀ Γ₁ := Ctx.subst_congr (fun a ha =>
        renameBlock_append_find m _ (hout a (List.mem_append_left _ ha)))
      have hR : Ret.subst ψ R₁ = Ret.subst φ₀ R₁ := Ret.subst_congr (fun a ha =>
        renameBlock_append_find m _ (hout a (List.mem_append_right _ ha)))
      rw [← Scheme.subst_compose, ← Ctx.subst_compose, ← Ret.subst_compose, ← hΓ, ← hR,
        ← generalize_open ᾱ m φ₀, ← generalize_openPlus ᾱ m φ₀]
      refine ih₁ h₁ ψ _ (fun c hc => ?_)
      by_cases hg : c.ftv.any (· ∈ ᾱ) = true
      · exact .inr (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, hg⟩)))
      · have hr : c ∈ o₁.plus.filter (fun c => !c.ftv.any (· ∈ ᾱ)) :=
          List.mem_filter.mpr ⟨hc, by simpa using hg⟩
        have hc' : c.subst ψ = c.subst φ₀ := Ty.subst_congr (fun a ha =>
          renameBlock_append_find m _ (fun hα => hg (List.any_eq_true.mpr ⟨a, ha, by simpa using hα⟩)))
        rw [hc']
        exact (hsat.1 c hr).weaken _
    · simp only [Prod.mk.injEq] at hls; obtain ⟨rfl, rfl⟩ := hls
      refine .let_ _ [] (fun m _ => ?_) (.inl ⟨rfl, by simp [Scheme.mono, Scheme.subst]⟩) he₂
      simpa using ih₁ h₁ _ C hsat.1
  | cond c t e ihc iht ihe =>
    intro Γ R n o h φ C hsat
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
    have hc := ihc h₁ _ C hsat.1.1
    have ht := iht h₂ _ C hsat.1.2
    have he := ihe h₃ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at hc ht he ⊢
    rw [unify_sound hu] at ht
    exact .cond hc ht he
  | unop op e ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    cases op with
    | not =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .not (ih h₁ φ C hsat)
    | typeof =>
      simp only [Option.some.injEq] at h; subst h
      exact .unop .typeof (ih h₁ φ C hsat)
    | neg =>
      simp only at h
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have he := ih h₁ _ C hsat
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he ⊢
      rw [unify_sound hu] at he
      exact .unop .neg he
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o h φ C hsat
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
      have he₁ := ih₁ h₁ _ C hsat.1.1
      have he₂ := ih₂ h₂ _ C hsat.1.2
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ hsat ⊢
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
      have he₁ := ih₁ h₁ _ C hsat.1
      have he₂ := ih₂ h₂ _ C hsat.2
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
      rw [unify_sound hu₃] at he₁
      rw [unify_sound hu₄] at he₂
      exact .binop .minus (by simpa using he₁) (by simpa using he₂)
  | ret e ih =>
    intro Γ R n o h φ C hsat
    cases R with
    | none => simp [infer] at h
    | some τr =>
      simp only [infer] at h
      split at h
      · cases h
      rename_i o₁ h₁
      split at h
      · cases h
      rename_i σ' hu
      simp only [Option.some.injEq] at h; subst h
      simp only [Sat.map] at hsat
      have he := ih h₁ _ C hsat
      simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_some] at he ⊢
      rw [← unify_sound hu] at he
      exact .ret he
  | throw_ e ih =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    simp only [Option.some.injEq] at h; subst h
    exact .throw_ (ih h₁ φ C hsat)
  | seq e₁ e₂ ih₁ ih₂ =>
    intro Γ R n o h φ C hsat
    simp only [infer] at h
    split at h
    · cases h
    rename_i o₁ h₁
    split at h
    · cases h
    rename_i o₂ h₂
    simp only [Option.some.injEq] at h; subst h
    simp only [Sat.map, Sat.append] at hsat
    have he₁ := ih₁ h₁ _ C hsat.1
    have he₂ := ih₂ h₂ _ C hsat.2
    simp only [Ty.subst_compose, Ctx.subst_compose, Ret.subst_compose] at he₁ he₂ ⊢
    exact .seq he₁ he₂

/-- A program inference accepts is well typed. -/
theorem inferProgram_sound {e : Expr} {τ : Ty} (h : inferProgram e = some τ) :
    HasType [] [] none e τ := by
  simp only [inferProgram] at h
  split at h
  · cases h
  rename_i o ho
  split at h
  · rename_i hall
    simp only [Option.some.injEq] at h; subst h
    have hsat : Sat [] o.plus [] := fun c hc => by
      have := List.all_eq_true.mp hall c hc
      refine .inl ?_
      cases c <;> simp_all [Ty.isPlusInst] <;> constructor
    simpa using infer_sound ho [] [] hsat
  · cases h

/-- A program inference accepts never gets stuck, whatever the fuel. -/
theorem inferProgram_never_stuck {e : Expr} {τ : Ty} (h : inferProgram e = some τ)
    (fuel : Nat) (s : Stuck) : eval fuel [] e ≠ .stuck s :=
  never_stuck (inferProgram_sound h) fuel s

end Inty
