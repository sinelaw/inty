import Inty.Subst

/-!
# Unification

Robinson unification on a worklist of equations, terminating by the number
of variables still to eliminate and then the size of the equations. `vs`
lists the variables that may still be bound; binding one removes it, which
is what makes the recursion well founded without a set library. The
results: `unify_sound` (the unifier equates the two types) and `unify_mgu`
(every other unifier factors through it), which completeness of inference
rests on.
-/

namespace Inty

mutual
/-- The number of constructors in a type. -/
def Ty.size : Ty → Nat
  | .var _ => 1
  | .app _ args => 1 + Ty.sizes args
def Ty.sizes : List Ty → Nat
  | [] => 0
  | τ :: τs => τ.size + Ty.sizes τs
end

theorem Ty.size_pos (τ : Ty) : 0 < τ.size := by
  cases τ <;> simp [Ty.size] <;> omega

/-- The total size of a list of equations. -/
def eqsSize : List (Ty × Ty) → Nat
  | [] => 0
  | (a, b) :: eqs => a.size + b.size + eqsSize eqs

theorem eqsSize_zip : ∀ (ps₁ ps₂ : List Ty), ps₁.length = ps₂.length →
    eqsSize (ps₁.zip ps₂) = Ty.sizes ps₁ + Ty.sizes ps₂
  | [], [], _ => rfl
  | p₁ :: ps₁, p₂ :: ps₂, h => by
    simp only [List.zip_cons_cons, eqsSize, Ty.sizes,
      eqsSize_zip ps₁ ps₂ (by simpa using h)]
    omega

theorem eqsSize_append (e₁ e₂ : List (Ty × Ty)) : eqsSize (e₁ ++ e₂) = eqsSize e₁ + eqsSize e₂ := by
  induction e₁ with
  | nil => simp [eqsSize]
  | cons e e₁ ih => obtain ⟨a, b⟩ := e; simp only [List.cons_append, eqsSize, ih]; omega

/-- Substitute in both sides of each equation. -/
def substEqs (σ : Subst) (eqs : List (Ty × Ty)) : List (Ty × Ty) :=
  eqs.map fun e => (e.1.subst σ, e.2.subst σ)

/-- A variable on one side, to be bound to the other side. -/
def orient : Ty → Ty → Option (Nat × Ty)
  | .var a, τ => some (a, τ)
  | τ, .var a => some (a, τ)
  | _, _ => none

private theorem lex_left {a a' b b' : Nat} (h : a' < a) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := .left _ _ h

private theorem lex_right {a b b' : Nat} (h : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a, b') (a, b) := .right _ h

/-- Unify a list of equations, binding only variables in `vs`. -/
def unifyEqs (vs : List Nat) (eqs : List (Ty × Ty)) : Option Subst :=
  match eqs with
  | [] => some []
  | (τ₁, τ₂) :: eqs =>
    if τ₁ = τ₂ then unifyEqs vs eqs
    else
      match orient τ₁ τ₂ with
      | some (a, τ) =>
        if a ∈ τ.ftv then none
        else if _h : a ∈ vs then
          (unifyEqs (vs.erase a) (substEqs [(a, τ)] eqs)).map (Subst.compose · [(a, τ)])
        else none
      | none =>
        match τ₁, τ₂ with
        -- The same constructor: its arguments pairwise.
        | .app c₁ as₁, .app c₂ as₂ =>
          if c₁ = c₂ ∧ as₁.length = as₂.length then
            unifyEqs vs (as₁.zip as₂ ++ eqs)
          else none
        | _, _ => none
termination_by (vs.length, eqsSize eqs)
decreasing_by
  · exact lex_right (by simp only [eqsSize]; have := Ty.size_pos τ₁; have := Ty.size_pos τ₂; omega)
  · exact lex_left (by
      have := List.length_erase_of_mem ‹_ ∈ vs›; have := List.length_pos_of_mem ‹_ ∈ vs›; omega)
  · refine lex_right ?_
    simp only [eqsSize, eqsSize_append, eqsSize_zip _ _ (‹_ ∧ _›).2, Ty.size]
    omega

/-- A most general unifier of two types, if they unify. -/
def unify (τ₁ τ₂ : Ty) : Option Subst := unifyEqs (τ₁.ftv ++ τ₂.ftv) [(τ₁, τ₂)]


/-! ## Lemmas -/

theorem Ty.sizes_eq (τs : List Ty) : Ty.sizes τs = (τs.map Ty.size).sum := by
  induction τs <;> simp_all [Ty.sizes]

theorem Ty.size_le_sizes {p : Ty} {ps : List Ty} (h : p ∈ ps) : p.size ≤ Ty.sizes ps := by
  induction ps with
  | nil => cases h
  | cons q ps ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [Ty.sizes]
    · have := ih h; simp [Ty.sizes]; omega

/-- A variable's image is no bigger than the image of a type it occurs in. -/
theorem Ty.size_subst_var_le (ψ : Subst) {x : Nat} :
    ∀ {τ : Ty}, x ∈ τ.ftv → ((Ty.var x).subst ψ).size ≤ (τ.subst ψ).size := by
  intro τ
  induction τ using Ty.ind with
  | var a => intro h; simp at h; subst h; exact Nat.le_refl _
  | app c args ih =>
    intro h
    simp only [Ty.ftv_app, List.mem_flatMap] at h
    simp only [Ty.subst_app, Ty.size, Ty.sizes_eq]
    obtain ⟨p, hp, h⟩ := h
    have := ih p hp h
    have := Ty.size_le_sizes (List.mem_map_of_mem (f := fun x => x.subst ψ) hp)
    rw [Ty.sizes_eq] at this
    omega

/-- The occurs check is right: a variable never unifies with a type that
properly contains it. -/
theorem Ty.subst_ne_of_occurs (ψ : Subst) {x : Nat} {τ : Ty} (hx : x ∈ τ.ftv)
    (hne : τ ≠ .var x) : (Ty.var x).subst ψ ≠ τ.subst ψ := by
  intro heq
  cases τ with
  | var a => simp at hx; subst hx; exact hne rfl
  | app c args =>
    have hle : ((Ty.var x).subst ψ).size ≤ ((Ty.app c args).subst ψ).size - 1 := by
      simp only [Ty.ftv_app, List.mem_flatMap] at hx
      simp only [Ty.subst_app, Ty.size]
      obtain ⟨p, hp, h⟩ := hx
      have := Ty.size_subst_var_le ψ h
      have := Ty.size_le_sizes (List.mem_map_of_mem (f := fun x => x.subst ψ) hp)
      omega
    rw [heq] at hle
    have := Ty.size_pos ((Ty.app c args).subst ψ)
    omega

/-- A single binding `a ↦ τ`, with `a` not in `τ`, leaves `τ` alone. -/
theorem Ty.subst_single {a : Nat} {τ : Ty} (h : a ∉ τ.ftv) : τ.subst [(a, τ)] = τ :=
  Ty.subst_id (fun b hb => by
    have : b ≠ a := fun e => h (e ▸ hb)
    simp [Subst.find, this])

/-- If `ψ` already sends `x` where `x ↦ τ` does, then `x ↦ τ` before `ψ` is
just `ψ`. -/
theorem Ty.subst_single_absorb {ψ : Subst} {x : Nat} {τ : Ty}
    (h : (Ty.var x).subst ψ = τ.subst ψ) (ρ : Ty) :
    (ρ.subst [(x, τ)]).subst ψ = ρ.subst ψ := by
  induction ρ using Ty.ind with
  | var a =>
    by_cases hax : a = x
    · subst hax; simpa [Ty.subst, Subst.find] using h.symm
    · simp [Ty.subst, Subst.find, hax]
  | app c args ih =>
    simp only [Ty.subst_app, List.map_map, Ty.app.injEq, true_and]
    exact List.map_congr_left ih

/-- The variables of `ρ` with `x ↦ τ` applied. -/
theorem Ty.ftv_subst_single {x a : Nat} {τ : Ty} {ρ : Ty} (h : a ∈ (ρ.subst [(x, τ)]).ftv) :
    (a ∈ ρ.ftv ∧ a ≠ x) ∨ a ∈ τ.ftv := by
  induction ρ using Ty.ind with
  | var b =>
    by_cases hbx : b = x
    · subst hbx; simp [Ty.subst, Subst.find] at h; exact .inr h
    · simp [Ty.subst, Subst.find, hbx] at h; subst h; exact .inl ⟨by simp, hbx⟩
  | app c args ih =>
    simp only [Ty.subst_app, Ty.ftv_app, List.mem_flatMap, List.mem_map] at h ⊢
    obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := h
    rcases ih p hp h with ⟨h, hne⟩ | h
    · exact .inl ⟨⟨p, hp, h⟩, hne⟩
    · exact .inr h

theorem orient_spec {τ₁ τ₂ τ : Ty} {x : Nat} (h : orient τ₁ τ₂ = some (x, τ)) :
    (τ₁ = .var x ∧ τ₂ = τ) ∨ (τ₂ = .var x ∧ τ₁ = τ) := by
  unfold orient at h
  split at h <;> simp_all

theorem map_eq_of_zip : ∀ {ps₁ ps₂ : List Ty} {σ : Subst}, ps₁.length = ps₂.length →
    (∀ p ∈ ps₁.zip ps₂, p.1.subst σ = p.2.subst σ) → ps₁.map (·.subst σ) = ps₂.map (·.subst σ)
  | [], [], _, _, _ => rfl
  | p₁ :: ps₁, p₂ :: ps₂, σ, hlen, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h (p₁, p₂) (by simp), map_eq_of_zip (by simpa using hlen)
      (fun p hp => h p (by simp [hp]))⟩

theorem zip_of_map_eq : ∀ {ps₁ ps₂ : List Ty} {σ : Subst},
    ps₁.map (·.subst σ) = ps₂.map (·.subst σ) → ∀ p ∈ ps₁.zip ps₂, p.1.subst σ = p.2.subst σ
  | [], _, _, _, _, hp => by simp at hp
  | _ :: _, [], _, _, _, hp => by simp at hp
  | p₁ :: ps₁, p₂ :: ps₂, σ, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h.1
    · exact zip_of_map_eq h.2 p hp

/-! ## Soundness -/

theorem unifyEqs_sound :
    ∀ (vs : List Nat) (eqs : List (Ty × Ty)) {σ : Subst}, unifyEqs vs eqs = some σ →
      ∀ e ∈ eqs, e.1.subst σ = e.2.subst σ := by
  intro vs eqs
  induction vs, eqs using unifyEqs.induct with
  | case1 => intro σ _ e he; cases he
  | case2 vs b eqs ih =>
    intro σ h e he
    unfold unifyEqs at h; simp only [ite_true] at h
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih h e he
  | case3 vs a b eqs hab x τ ho hocc =>
    intro σ h; unfold unifyEqs at h; simp [hab, ho, hocc] at h
  | case4 vs a b eqs hab x τ ho hocc hx ih =>
    intro σ h e he
    unfold unifyEqs at h; simp only [hab, ho, hocc, hx, ite_false, dite_true] at h
    obtain ⟨σ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    have ih' := ih h'
    rcases List.mem_cons.mp he with rfl | he
    · rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [Ty.subst_compose, Ty.subst_single hocc]; simp [Ty.subst, Subst.find]
      · simp only [Ty.subst_compose, Ty.subst_single hocc]; simp [Ty.subst, Subst.find]
    · have := ih' _ (List.mem_map_of_mem (f := fun e => (e.1.subst [(x, τ)], e.2.subst [(x, τ)])) he)
      simpa [Ty.subst_compose] using this
  | case5 vs a b eqs hab x τ ho hocc hx =>
    intro σ h; unfold unifyEqs at h; simp [hab, ho, hocc, hx] at h
  | case6 vs eqs c₁ as₁ c₂ as₂ hc hne ho ih =>
    intro σ h e he
    unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_true hc, ite_true] at h
    have ih' := ih h
    rcases List.mem_cons.mp he with rfl | he
    · simp only [Ty.subst_app, Ty.app.injEq]
      exact ⟨hc.1, map_eq_of_zip hc.2 (fun p hp => ih' p (by simp [hp]))⟩
    · exact ih' e (by simp [he])
  | case7 vs eqs c₁ as₁ c₂ as₂ hc hne ho =>
    intro σ h; unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_false hc] at h; cases h
  | case8 vs a b eqs hab ho happ =>
    intro σ h
    unfold unifyEqs at h; simp only [hab, ho, ite_false] at h
    cases a <;> cases b <;> simp_all

theorem unify_sound {τ₁ τ₂ : Ty} {σ : Subst} (h : unify τ₁ τ₂ = some σ) :
    τ₁.subst σ = τ₂.subst σ :=
  unifyEqs_sound _ _ h (τ₁, τ₂) (by simp)

/-! ## Most general -/

/-- Every unifier `ψ` of the equations factors through the one found: `ψ`
after `σ` is `ψ`. So unification succeeds whenever anything unifies the
equations, given that `vs` has all their variables. -/
theorem unifyEqs_mgu :
    ∀ (vs : List Nat) (eqs : List (Ty × Ty)),
      (∀ e ∈ eqs, ∀ a, a ∈ e.1.ftv ∨ a ∈ e.2.ftv → a ∈ vs) →
      ∀ {ψ : Subst}, (∀ e ∈ eqs, e.1.subst ψ = e.2.subst ψ) →
        ∃ σ, unifyEqs vs eqs = some σ ∧ ∀ τ : Ty, (τ.subst σ).subst ψ = τ.subst ψ := by
  intro vs eqs
  induction vs, eqs using unifyEqs.induct with
  | case1 => intro _ ψ _; exact ⟨[], by simp [unifyEqs], by simp⟩
  | case2 vs b eqs ih =>
    intro hvs ψ hψ
    obtain ⟨σ, h, hσ⟩ := ih (fun e he => hvs e (by simp [he])) (fun e he => hψ e (by simp [he]))
    exact ⟨σ, by unfold unifyEqs; simpa using h, hσ⟩
  | case3 vs a b eqs hab x τ ho hocc =>
    intro _ ψ hψ
    have h₀ := hψ (a, b) (by simp)
    rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h₀ (Ty.subst_ne_of_occurs ψ hocc (Ne.symm hab))
    · exact absurd h₀.symm (Ty.subst_ne_of_occurs ψ hocc hab)
  | case4 vs a b eqs hab x τ ho hocc hx ih =>
    intro hvs ψ hψ
    have h₀ : (Ty.var x).subst ψ = τ.subst ψ := by
      have := hψ (a, b) (by simp)
      rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
    have hτvs : ∀ c ∈ τ.ftv, c ∈ vs := fun c hc => by
      rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvs _ List.mem_cons_self c (.inr hc)
      · exact hvs _ List.mem_cons_self c (.inl hc)
    have hvs' : ∀ e ∈ substEqs [(x, τ)] eqs, ∀ c, c ∈ e.1.ftv ∨ c ∈ e.2.ftv → c ∈ vs.erase x := by
      intro e he c hc
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      have hmem : ∀ ρ, (ρ = e₀.1 ∨ ρ = e₀.2) → c ∈ (ρ.subst [(x, τ)]).ftv → c ∈ vs.erase x := by
        intro ρ hρ hc
        rcases Ty.ftv_subst_single hc with ⟨hc, hne⟩ | hc
        · refine (List.mem_erase_of_ne hne).mpr (hvs e₀ (by simp [he₀]) c ?_)
          rcases hρ with rfl | rfl
          · exact .inl hc
          · exact .inr hc
        · exact (List.mem_erase_of_ne (fun e : c = x => hocc (e ▸ hc))).mpr (hτvs c hc)
      rcases hc with hc | hc
      · exact hmem _ (.inl rfl) hc
      · exact hmem _ (.inr rfl) hc
    have hψ' : ∀ e ∈ substEqs [(x, τ)] eqs, e.1.subst ψ = e.2.subst ψ := by
      intro e he
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      simp only [Ty.subst_single_absorb h₀]
      exact hψ e₀ (by simp [he₀])
    obtain ⟨σ', h', hσ'⟩ := ih hvs' hψ'
    refine ⟨Subst.compose σ' [(x, τ)], ?_, fun ρ => ?_⟩
    · unfold unifyEqs; simp [hab, ho, hocc, hx, h']
    · rw [Ty.subst_compose, hσ', Ty.subst_single_absorb h₀]
  | case5 vs a b eqs hab x τ ho hocc hx =>
    intro hvs _ _
    rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (hvs _ List.mem_cons_self x (.inl (by simp [Ty.ftv]))) hx
    · exact absurd (hvs _ List.mem_cons_self x (.inr (by simp [Ty.ftv]))) hx
  | case6 vs eqs c₁ as₁ c₂ as₂ hc hne ho ih =>
    intro hvs ψ hψ
    have h₀ := hψ _ List.mem_cons_self
    simp only [Ty.subst_app, Ty.app.injEq] at h₀
    have hfv : ∀ c, c ∈ (Ty.app c₁ as₁).ftv ∨ c ∈ (Ty.app c₂ as₂).ftv → c ∈ vs :=
      hvs _ List.mem_cons_self
    simp only [Ty.ftv_app, List.mem_flatMap] at hfv
    obtain ⟨σ, h, hσ⟩ := ih (ψ := ψ)
      (fun e he c hc => by
        rcases List.mem_append.mp he with he | he
        · rcases hc with hc | hc
          · exact hfv c (.inl ⟨_, (List.of_mem_zip he).1, hc⟩)
          · exact hfv c (.inr ⟨_, (List.of_mem_zip he).2, hc⟩)
        · exact hvs e (by simp [he]) c hc)
      (fun e he => by
        rcases List.mem_append.mp he with he | he
        · exact zip_of_map_eq h₀.2 e he
        · exact hψ e (by simp [he]))
    exact ⟨σ, by unfold unifyEqs; simp only [hne, ho, ite_false, eq_true hc, ite_true]; exact h, hσ⟩
  | case7 vs eqs c₁ as₁ c₂ as₂ hc hne ho =>
    intro _ ψ hψ
    have h₀ := hψ _ List.mem_cons_self
    simp only [Ty.subst_app, Ty.app.injEq] at h₀
    exact absurd ⟨h₀.1, by simpa using congrArg List.length h₀.2⟩ hc
  | case8 vs a b eqs hab ho happ =>
    intro _ ψ hψ
    have h₀ := hψ (a, b) (by simp)
    cases a <;> cases b <;> first
      | exact absurd (happ _ _ _ _ rfl rfl) id
      | simp_all [orient]

/-- Unification succeeds whenever the types unify, with a most general
unifier. -/
theorem unify_mgu {τ₁ τ₂ : Ty} {ψ : Subst} (h : τ₁.subst ψ = τ₂.subst ψ) :
    ∃ σ, unify τ₁ τ₂ = some σ ∧ ∀ τ : Ty, (τ.subst σ).subst ψ = τ.subst ψ :=
  unifyEqs_mgu _ _ (fun e he c hc => by
    simp only [List.mem_singleton] at he; subst he
    simp only [List.mem_append]; exact hc) (fun e he => by
    simp only [List.mem_singleton] at he; subst he; exact h)

end Inty
