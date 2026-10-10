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

This is syntactic unification: two recursive types unify only if their
equations do, equation by equation, so the equations are `RTy`s, which
take a recursive type's equations apart as well (`self j` against
`self j`). Equating recursive types by unfolding is `Inty.Equi`'s.
-/

namespace Inty

mutual
/-- The number of constructors in an equation's right-hand side. -/
def RTy.size : RTy → Nat
  | .free _ | .self _ => 1
  | .app _ args => 1 + RTy.sizes args
  | .mu _ sys => 1 + RTy.sizes sys
def RTy.sizes : List RTy → Nat
  | [] => 0
  | r :: rs => r.size + RTy.sizes rs
end

theorem RTy.size_pos (r : RTy) : 0 < r.size := by
  cases r <;> simp [RTy.size] <;> omega

/-- The total size of a list of equations. -/
def eqsSize : List (RTy × RTy) → Nat
  | [] => 0
  | (a, b) :: eqs => a.size + b.size + eqsSize eqs

theorem eqsSize_zip : ∀ (ps₁ ps₂ : List RTy), ps₁.length = ps₂.length →
    eqsSize (ps₁.zip ps₂) = RTy.sizes ps₁ + RTy.sizes ps₂
  | [], [], _ => rfl
  | p₁ :: ps₁, p₂ :: ps₂, h => by
    simp only [List.zip_cons_cons, eqsSize, RTy.sizes,
      eqsSize_zip ps₁ ps₂ (by simpa using h)]
    omega

theorem eqsSize_append (e₁ e₂ : List (RTy × RTy)) :
    eqsSize (e₁ ++ e₂) = eqsSize e₁ + eqsSize e₂ := by
  induction e₁ with
  | nil => simp [eqsSize]
  | cons e e₁ ih => obtain ⟨a, b⟩ := e; simp only [List.cons_append, eqsSize, ih]; omega

/-- Substitute in both sides of each equation. -/
def substEqs (σ : Subst) (eqs : List (RTy × RTy)) : List (RTy × RTy) :=
  eqs.map fun e => (e.1.subst σ, e.2.subst σ)

mutual
/-- A right-hand side as a type: it has no `self` but inside a `mu` of its
own. -/
def RTy.toTy? : RTy → Option Ty
  | .free a => some (.var a)
  | .self _ => none
  | .app c args => (RTy.toTys? args).map (.app c)
  | .mu i sys => some (.mu i sys)
def RTy.toTys? : List RTy → Option (List Ty)
  | [] => some []
  | r :: rs =>
    match r.toTy?, RTy.toTys? rs with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none
end

/-- A variable on one side, to be bound to the other side. -/
def orient : RTy → RTy → Option (Nat × RTy)
  | .free a, r => some (a, r)
  | r, .free a => some (a, r)
  | _, _ => none

private theorem lex_left {a a' b b' : Nat} (h : a' < a) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := .left _ _ h

private theorem lex_right {a b b' : Nat} (h : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a, b') (a, b) := .right _ h

/-- Unify a list of equations, binding only variables in `vs`. -/
def unifyEqs (vs : List Nat) (eqs : List (RTy × RTy)) : Option Subst :=
  match eqs with
  | [] => some []
  | (r₁, r₂) :: eqs =>
    if r₁ = r₂ then unifyEqs vs eqs
    else
      match orient r₁ r₂ with
      | some (a, r) =>
        if a ∈ r.ftv then none
        else
          match r.toTy? with
          | none => none
          | some τ =>
            if _h : a ∈ vs then
              (unifyEqs (vs.erase a) (substEqs [(a, τ)] eqs)).map (Subst.compose · [(a, τ)])
            else none
      | none =>
        match r₁, r₂ with
        -- The same constructor: its arguments pairwise.
        | .app c₁ as₁, .app c₂ as₂ =>
          if c₁ = c₂ ∧ as₁.length = as₂.length then
            unifyEqs vs (as₁.zip as₂ ++ eqs)
          else none
        -- The same type of a system of as many equations: the equations
        -- pairwise.
        | .mu i₁ s₁, .mu i₂ s₂ =>
          if i₁ = i₂ ∧ s₁.length = s₂.length then
            unifyEqs vs (s₁.zip s₂ ++ eqs)
          else none
        | _, _ => none
termination_by (vs.length, eqsSize eqs)
decreasing_by
  · exact lex_right (by simp only [eqsSize]; have := RTy.size_pos r₁; have := RTy.size_pos r₂; omega)
  · exact lex_left (by
      have := List.length_erase_of_mem ‹_ ∈ vs›; have := List.length_pos_of_mem ‹_ ∈ vs›; omega)
  · refine lex_right ?_
    simp only [eqsSize, eqsSize_append, eqsSize_zip _ _ (‹_ ∧ _›).2, RTy.size]
    omega
  · refine lex_right ?_
    simp only [eqsSize, eqsSize_append, eqsSize_zip _ _ (‹_ ∧ _›).2, RTy.size]
    omega

/-- A most general unifier of two types, if they unify. -/
def unify (τ₁ τ₂ : Ty) : Option Subst :=
  unifyEqs (τ₁.ftv ++ τ₂.ftv) [(τ₁.toRTy, τ₂.toRTy)]

/-! ## Lemmas -/

theorem RTy.sizes_eq (rs : List RTy) : RTy.sizes rs = (rs.map RTy.size).sum := by
  induction rs <;> simp_all [RTy.sizes]

theorem RTy.size_le_sizes {p : RTy} {ps : List RTy} (h : p ∈ ps) : p.size ≤ RTy.sizes ps := by
  induction ps with
  | nil => cases h
  | cons q ps ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [RTy.sizes]
    · have := ih h; simp [RTy.sizes]; omega

theorem Ty.toRTy_toTy? (τ : Ty) : τ.toRTy.toTy? = some τ := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    have : RTy.toTys? (args.map Ty.toRTy) = some args := by
      induction args with
      | nil => rfl
      | cons τ τs ihl =>
        simp only [List.map_cons, RTy.toTys?, ih τ List.mem_cons_self,
          ihl (fun p hp => ih p (List.mem_cons_of_mem _ hp))]
    simp [Ty.toRTy_app, RTy.toTy?, this]
  | mu i sys => rfl

theorem RTy.toTy?_spec {r : RTy} {τ : Ty} (h : r.toTy? = some τ) : r = τ.toRTy := by
  induction r using RTy.ind generalizing τ with
  | free a => simp [RTy.toTy?] at h; subst h; rfl
  | self j => simp [RTy.toTy?] at h
  | app c args ih =>
    simp only [RTy.toTy?, Option.map_eq_some_iff] at h
    obtain ⟨τs, hτs, rfl⟩ := h
    simp only [Ty.toRTy_app, RTy.app.injEq, true_and]
    induction args generalizing τs with
    | nil => simp [RTy.toTys?] at hτs; subst hτs; rfl
    | cons r rs ihl =>
      unfold RTy.toTys? at hτs
      split at hτs
      · rename_i τ τs' hr hrs
        cases hτs
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨ih r List.mem_cons_self hr,
          ihl (fun p hp => ih p (List.mem_cons_of_mem _ hp)) τs' hrs⟩
      · cases hτs
  | mu i sys => simp [RTy.toTy?] at h; subst h; rfl

theorem Ty.toRTy_inj {τ₁ τ₂ : Ty} (h : τ₁.toRTy = τ₂.toRTy) : τ₁ = τ₂ := by
  have := Ty.toRTy_toTy? τ₁
  rw [h, Ty.toRTy_toTy?] at this
  exact (Option.some.inj this).symm

@[simp] theorem Ty.toRTy_ftv (τ : Ty) : τ.toRTy.ftv = τ.ftv := by
  induction τ using Ty.ind with
  | var a => rfl
  | app c args ih =>
    simp only [Ty.toRTy_app, RTy.ftv_app, List.flatMap_map, Ty.ftv_app]
    simp only [List.flatMap]
    congr 1
    exact List.map_congr_left ih
  | mu i sys => simp [Ty.toRTy]

/-- A `self` outside any `mu` of its own stays through substitution. -/
theorem RTy.toTy?_subst_none (ψ : Subst) {r : RTy} (h : r.toTy? = none) :
    (r.subst ψ).toTy? = none := by
  induction r using RTy.ind with
  | free a => simp [RTy.toTy?] at h
  | self j => rfl
  | app c args ih =>
    simp only [RTy.toTy?, Option.map_eq_none_iff] at h
    simp only [RTy.subst_app, RTy.toTy?, Option.map_eq_none_iff]
    induction args with
    | nil => simp [RTy.toTys?] at h
    | cons r rs ihl =>
      unfold RTy.toTys? at h
      simp only [List.map_cons]
      unfold RTy.toTys?
      split at h
      · cases h
      · rename_i hn
        split
        · rename_i τ τs hr hrs
          cases hr' : r.toTy? with
          | none => rw [ih r List.mem_cons_self hr'] at hr; cases hr
          | some τ₀ =>
            cases hrs' : RTy.toTys? rs with
            | none =>
              rw [ihl (fun p hp => ih p (List.mem_cons_of_mem _ hp)) hrs'] at hrs; cases hrs
            | some τs₀ => exact (hn τ₀ τs₀ hr' hrs').elim
        · rfl
  | mu i sys => simp [RTy.toTy?] at h

/-- A variable's image is no bigger than the image of a right-hand side it
occurs in. -/
theorem RTy.size_subst_var_le (ψ : Subst) {x : Nat} :
    ∀ {r : RTy}, x ∈ r.ftv → ((RTy.free x).subst ψ).size ≤ (r.subst ψ).size := by
  intro r
  induction r using RTy.ind with
  | free a => intro h; simp [RTy.ftv] at h; subst h; exact Nat.le_refl _
  | self j => intro h; simp [RTy.ftv] at h
  | app c args ih =>
    intro h
    simp only [RTy.ftv_app, List.mem_flatMap] at h
    simp only [RTy.subst_app, RTy.size, RTy.sizes_eq]
    obtain ⟨p, hp, h⟩ := h
    have := ih p hp h
    have := RTy.size_le_sizes (List.mem_map_of_mem (f := fun x => x.subst ψ) hp)
    rw [RTy.sizes_eq] at this
    omega
  | mu i sys ih =>
    intro h
    simp only [RTy.ftv_mu, List.mem_flatMap] at h
    simp only [RTy.subst_mu, RTy.size, RTy.sizes_eq]
    obtain ⟨p, hp, h⟩ := h
    have := ih p hp h
    have := RTy.size_le_sizes (List.mem_map_of_mem (f := fun x => x.subst ψ) hp)
    rw [RTy.sizes_eq] at this
    omega

/-- The occurs check is right: a variable never unifies with a right-hand
side that properly contains it. -/
theorem RTy.subst_ne_of_occurs (ψ : Subst) {x : Nat} {r : RTy} (hx : x ∈ r.ftv)
    (hne : r ≠ .free x) : (RTy.free x).subst ψ ≠ r.subst ψ := by
  intro heq
  cases r with
  | free a => simp [RTy.ftv] at hx; subst hx; exact hne rfl
  | self j => simp [RTy.ftv] at hx
  | app c args =>
    have hle : ((RTy.free x).subst ψ).size ≤ ((RTy.app c args).subst ψ).size - 1 := by
      simp only [RTy.ftv_app, List.mem_flatMap] at hx
      simp only [RTy.subst_app, RTy.size]
      obtain ⟨p, hp, h⟩ := hx
      have := RTy.size_subst_var_le ψ h
      have := RTy.size_le_sizes (List.mem_map_of_mem (f := fun x => x.subst ψ) hp)
      omega
    rw [heq] at hle
    have := RTy.size_pos ((RTy.app c args).subst ψ)
    omega
  | mu i sys =>
    have hle : ((RTy.free x).subst ψ).size ≤ ((RTy.mu i sys).subst ψ).size - 1 := by
      simp only [RTy.ftv_mu, List.mem_flatMap] at hx
      simp only [RTy.subst_mu, RTy.size]
      obtain ⟨p, hp, h⟩ := hx
      have := RTy.size_subst_var_le ψ h
      have := RTy.size_le_sizes (List.mem_map_of_mem (f := fun x => x.subst ψ) hp)
      omega
    rw [heq] at hle
    have := RTy.size_pos ((RTy.mu i sys).subst ψ)
    omega

/-- A single binding `a ↦ τ`, with `a` not in `τ`, leaves `τ` alone. -/
theorem Ty.subst_single {a : Nat} {τ : Ty} (h : a ∉ τ.ftv) : τ.subst [(a, τ)] = τ :=
  Ty.subst_id (fun b hb => by
    have : b ≠ a := fun e => h (e ▸ hb)
    simp [Subst.find, this])

theorem RTy.subst_single {a : Nat} {r : RTy} {τ : Ty} (h : a ∉ r.ftv) : r.subst [(a, τ)] = r :=
  RTy.subst_id (fun b hb => by
    have : b ≠ a := fun e => h (e ▸ hb)
    simp [Subst.find, this])

/-- If `ψ` already sends `x` where `x ↦ τ` does, then `x ↦ τ` before `ψ` is
just `ψ`. -/
theorem RTy.subst_single_absorb {ψ : Subst} {x : Nat} {τ : Ty}
    (h : (Ty.var x).subst ψ = τ.subst ψ) (r : RTy) :
    (r.subst [(x, τ)]).subst ψ = r.subst ψ := by
  induction r using RTy.ind with
  | free a =>
    by_cases hax : a = x
    · subst hax
      simp only [RTy.subst, Subst.find, ite_true, Option.getD_some, Ty.toRTy_subst]
      rw [← h]; rfl
    · simp [RTy.subst, Subst.find, hax, Ty.toRTy]
  | self j => rfl
  | app c args ih =>
    simp only [RTy.subst_app, List.map_map, RTy.app.injEq, true_and]
    exact List.map_congr_left ih
  | mu i sys ih =>
    simp only [RTy.subst_mu, List.map_map, RTy.mu.injEq, true_and]
    exact List.map_congr_left ih

theorem Ty.subst_single_absorb {ψ : Subst} {x : Nat} {τ : Ty}
    (h : (Ty.var x).subst ψ = τ.subst ψ) (ρ : Ty) :
    (ρ.subst [(x, τ)]).subst ψ = ρ.subst ψ := by
  apply Ty.toRTy_inj
  simp only [← Ty.toRTy_subst]
  exact RTy.subst_single_absorb h ρ.toRTy

/-- The variables of `r` with `x ↦ τ` applied. -/
theorem RTy.ftv_subst_single {x a : Nat} {τ : Ty} {r : RTy} (h : a ∈ (r.subst [(x, τ)]).ftv) :
    (a ∈ r.ftv ∧ a ≠ x) ∨ a ∈ τ.ftv := by
  induction r using RTy.ind with
  | free b =>
    by_cases hbx : b = x
    · subst hbx; simp [RTy.subst, Subst.find] at h; exact .inr h
    · simp only [RTy.subst, Subst.find, hbx, ite_false, Option.getD_none, Ty.toRTy] at h
      simp only [RTy.ftv, List.mem_singleton] at h; subst h
      exact .inl ⟨by simp [RTy.ftv], hbx⟩
  | self j => simp [RTy.subst, RTy.ftv] at h
  | app c args ih =>
    simp only [RTy.subst_app, RTy.ftv_app, List.mem_flatMap, List.mem_map] at h ⊢
    obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := h
    rcases ih p hp h with ⟨h, hne⟩ | h
    · exact .inl ⟨⟨p, hp, h⟩, hne⟩
    · exact .inr h
  | mu i sys ih =>
    simp only [RTy.subst_mu, RTy.ftv_mu, List.mem_flatMap, List.mem_map] at h ⊢
    obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := h
    rcases ih p hp h with ⟨h, hne⟩ | h
    · exact .inl ⟨⟨p, hp, h⟩, hne⟩
    · exact .inr h

theorem orient_spec {r₁ r₂ r : RTy} {x : Nat} (h : orient r₁ r₂ = some (x, r)) :
    (r₁ = .free x ∧ r₂ = r) ∨ (r₂ = .free x ∧ r₁ = r) := by
  unfold orient at h
  split at h <;> simp_all

theorem map_eq_of_zip : ∀ {ps₁ ps₂ : List RTy} {σ : Subst}, ps₁.length = ps₂.length →
    (∀ p ∈ ps₁.zip ps₂, p.1.subst σ = p.2.subst σ) → ps₁.map (·.subst σ) = ps₂.map (·.subst σ)
  | [], [], _, _, _ => rfl
  | p₁ :: ps₁, p₂ :: ps₂, σ, hlen, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h (p₁, p₂) (by simp), map_eq_of_zip (by simpa using hlen)
      (fun p hp => h p (by simp [hp]))⟩

theorem zip_of_map_eq : ∀ {ps₁ ps₂ : List RTy} {σ : Subst},
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
    ∀ (vs : List Nat) (eqs : List (RTy × RTy)) {σ : Subst}, unifyEqs vs eqs = some σ →
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
  | case3 vs a b eqs hab x r ho hocc =>
    intro σ h; unfold unifyEqs at h; simp [hab, ho, hocc] at h
  | case4 vs a b eqs hab x r ho hocc hτ =>
    intro σ h; unfold unifyEqs at h; simp [hab, ho, hocc, hτ] at h
  | case5 vs a b eqs hab x r ho hocc τ hτ hx ih =>
    intro σ h e he
    unfold unifyEqs at h; simp only [hab, ho, hocc, hτ, hx, ite_false, dite_true] at h
    obtain ⟨σ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    have ih' := ih h'
    have hr := RTy.toTy?_spec hτ
    subst hr
    have hocc' : x ∉ τ.ftv := by simpa using hocc
    rcases List.mem_cons.mp he with rfl | he
    · rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [RTy.subst_compose, RTy.subst_single hocc]
        simp [RTy.subst, Subst.find]
      · simp only [RTy.subst_compose, RTy.subst_single hocc]
        simp [RTy.subst, Subst.find]
    · have := ih' _ (List.mem_map_of_mem
        (f := fun e => (e.1.subst [(x, τ)], e.2.subst [(x, τ)])) he)
      simpa [RTy.subst_compose] using this
  | case6 vs a b eqs hab x r ho hocc τ hτ hx =>
    intro σ h; unfold unifyEqs at h; simp [hab, ho, hocc, hτ, hx] at h
  | case7 vs eqs c₁ as₁ c₂ as₂ hc hne ho ih =>
    intro σ h e he
    unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_true hc, ite_true] at h
    have ih' := ih h
    rcases List.mem_cons.mp he with rfl | he
    · simp only [RTy.subst_app, RTy.app.injEq]
      exact ⟨hc.1, map_eq_of_zip hc.2 (fun p hp => ih' p (by simp [hp]))⟩
    · exact ih' e (by simp [he])
  | case8 vs eqs c₁ as₁ c₂ as₂ hc hne ho =>
    intro σ h; unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_false hc] at h; cases h
  | case9 vs eqs i₁ s₁ i₂ s₂ hc hne ho ih =>
    intro σ h e he
    unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_true hc, ite_true] at h
    have ih' := ih h
    rcases List.mem_cons.mp he with rfl | he
    · simp only [RTy.subst_mu, RTy.mu.injEq]
      exact ⟨hc.1, map_eq_of_zip hc.2 (fun p hp => ih' p (by simp [hp]))⟩
    · exact ih' e (by simp [he])
  | case10 vs eqs i₁ s₁ i₂ s₂ hc hne ho =>
    intro σ h; unfold unifyEqs at h; simp only [hne, ho, ite_false, eq_false hc] at h; cases h
  | case11 vs a b eqs hab ho happ hmu =>
    intro σ h
    unfold unifyEqs at h; simp only [hab, ho, ite_false] at h
    cases a <;> cases b <;> simp_all

theorem unify_sound {τ₁ τ₂ : Ty} {σ : Subst} (h : unify τ₁ τ₂ = some σ) :
    τ₁.subst σ = τ₂.subst σ := by
  have := unifyEqs_sound _ _ h (τ₁.toRTy, τ₂.toRTy) (by simp)
  simp only [Ty.toRTy_subst] at this
  exact Ty.toRTy_inj this

/-! ## Most general -/

/-- Every unifier `ψ` of the equations factors through the one found: `ψ`
after `σ` is `ψ`. So unification succeeds whenever anything unifies the
equations, given that `vs` has all their variables. -/
theorem unifyEqs_mgu :
    ∀ (vs : List Nat) (eqs : List (RTy × RTy)),
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
  | case3 vs a b eqs hab x r ho hocc =>
    intro _ ψ hψ
    have h₀ := hψ (a, b) (by simp)
    rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h₀ (RTy.subst_ne_of_occurs ψ hocc (Ne.symm hab))
    · exact absurd h₀.symm (RTy.subst_ne_of_occurs ψ hocc hab)
  | case4 vs a b eqs hab x r ho hocc hτ =>
    intro _ ψ hψ
    have h₀ := hψ (a, b) (by simp)
    have hl : ((RTy.free x).subst ψ).toTy? = some ((Ty.var x).subst ψ) := by
      simp only [RTy.subst]; exact Ty.toRTy_toTy? _
    have hr := RTy.toTy?_subst_none ψ hτ
    rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h₀, hr] at hl; cases hl
    · rw [← h₀, hr] at hl; cases hl
  | case5 vs a b eqs hab x r ho hocc τ hτ hx ih =>
    intro hvs ψ hψ
    have hr := RTy.toTy?_spec hτ
    subst hr
    have hocc' : x ∉ τ.ftv := by simpa using hocc
    have h₀ : (Ty.var x).subst ψ = τ.subst ψ := by
      have := hψ (a, b) (by simp)
      apply Ty.toRTy_inj
      rw [← Ty.toRTy_subst, ← Ty.toRTy_subst]
      rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
    have hτvs : ∀ c ∈ τ.ftv, c ∈ vs := fun c hc => by
      rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvs _ List.mem_cons_self c (.inr (by simpa using hc))
      · exact hvs _ List.mem_cons_self c (.inl (by simpa using hc))
    have hvs' : ∀ e ∈ substEqs [(x, τ)] eqs, ∀ c, c ∈ e.1.ftv ∨ c ∈ e.2.ftv → c ∈ vs.erase x := by
      intro e he c hc
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      have hmem : ∀ ρ, (ρ = e₀.1 ∨ ρ = e₀.2) → c ∈ (ρ.subst [(x, τ)]).ftv → c ∈ vs.erase x := by
        intro ρ hρ hc
        rcases RTy.ftv_subst_single hc with ⟨hc, hne⟩ | hc
        · refine (List.mem_erase_of_ne hne).mpr (hvs e₀ (by simp [he₀]) c ?_)
          rcases hρ with rfl | rfl
          · exact .inl hc
          · exact .inr hc
        · exact (List.mem_erase_of_ne (fun e : c = x => hocc' (e ▸ hc))).mpr (hτvs c hc)
      rcases hc with hc | hc
      · exact hmem _ (.inl rfl) hc
      · exact hmem _ (.inr rfl) hc
    have hψ' : ∀ e ∈ substEqs [(x, τ)] eqs, e.1.subst ψ = e.2.subst ψ := by
      intro e he
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      simp only [RTy.subst_single_absorb h₀]
      exact hψ e₀ (by simp [he₀])
    obtain ⟨σ', h', hσ'⟩ := ih hvs' hψ'
    refine ⟨Subst.compose σ' [(x, τ)], ?_, fun ρ => ?_⟩
    · unfold unifyEqs; simp [hab, ho, hocc', hτ, hx, h']
    · rw [Ty.subst_compose, hσ', Ty.subst_single_absorb h₀]
  | case6 vs a b eqs hab x r ho hocc τ hτ hx =>
    intro hvs _ _
    rcases orient_spec ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (hvs _ List.mem_cons_self x (.inl (by simp [RTy.ftv]))) hx
    · exact absurd (hvs _ List.mem_cons_self x (.inr (by simp [RTy.ftv]))) hx
  | case7 vs eqs c₁ as₁ c₂ as₂ hc hne ho ih =>
    intro hvs ψ hψ
    have h₀ := hψ _ List.mem_cons_self
    simp only [RTy.subst_app, RTy.app.injEq] at h₀
    have hfv : ∀ c, c ∈ (RTy.app c₁ as₁).ftv ∨ c ∈ (RTy.app c₂ as₂).ftv → c ∈ vs :=
      hvs _ List.mem_cons_self
    simp only [RTy.ftv_app, List.mem_flatMap] at hfv
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
  | case8 vs eqs c₁ as₁ c₂ as₂ hc hne ho =>
    intro _ ψ hψ
    have h₀ := hψ _ List.mem_cons_self
    simp only [RTy.subst_app, RTy.app.injEq] at h₀
    exact absurd ⟨h₀.1, by simpa using congrArg List.length h₀.2⟩ hc
  | case9 vs eqs i₁ s₁ i₂ s₂ hc hne ho ih =>
    intro hvs ψ hψ
    have h₀ := hψ _ List.mem_cons_self
    simp only [RTy.subst_mu, RTy.mu.injEq] at h₀
    have hfv : ∀ c, c ∈ (RTy.mu i₁ s₁).ftv ∨ c ∈ (RTy.mu i₂ s₂).ftv → c ∈ vs :=
      hvs _ List.mem_cons_self
    simp only [RTy.ftv_mu, List.mem_flatMap] at hfv
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
  | case10 vs eqs i₁ s₁ i₂ s₂ hc hne ho =>
    intro _ ψ hψ
    have h₀ := hψ _ List.mem_cons_self
    simp only [RTy.subst_mu, RTy.mu.injEq] at h₀
    exact absurd ⟨h₀.1, by simpa using congrArg List.length h₀.2⟩ hc
  | case11 vs a b eqs hab ho happ hmu =>
    intro _ ψ hψ
    have h₀ := hψ (a, b) (by simp)
    cases a <;> cases b <;> first
      | exact absurd (happ _ _ _ _ rfl rfl) id
      | exact absurd (hmu _ _ _ _ rfl rfl) id
      | simp_all [orient, RTy.subst]

/-- Unification succeeds whenever the types unify, with a most general
unifier. -/
theorem unify_mgu {τ₁ τ₂ : Ty} {ψ : Subst} (h : τ₁.subst ψ = τ₂.subst ψ) :
    ∃ σ, unify τ₁ τ₂ = some σ ∧ ∀ τ : Ty, (τ.subst σ).subst ψ = τ.subst ψ :=
  unifyEqs_mgu _ _ (fun e he c hc => by
    simp only [List.mem_singleton] at he; subst he
    simp only [List.mem_append, Ty.toRTy_ftv] at hc ⊢; exact hc) (fun e he => by
    simp only [List.mem_singleton] at he; subst he
    simp only [Ty.toRTy_subst, h])

end Inty
