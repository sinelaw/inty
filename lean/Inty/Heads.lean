import Inty.Equi

/-!
# Heads through substitution

A type's head constructor, once unfolded (`Ty.whnf`), survives
substituting types for its variables.
-/

namespace Inty

/-! ## Heads through substitution -/

theorem Ty.whnf_cases (t : Ty) :
    (∃ a, t.whnf = .var a) ∨ (∃ c xs, t.whnf = .app c xs ∧ t.view = some (.app c xs)) ∨
      t.view = none := by
  cases hv : t.view with
  | none => exact .inr (.inr rfl)
  | some v =>
    rcases Ty.view_shape hv with ⟨a, rfl⟩ | ⟨c, xs, rfl⟩
    · exact .inl ⟨a, Ty.whnf_of_view hv⟩
    · exact .inr (.inl ⟨c, xs, Ty.whnf_of_view hv, rfl⟩)

theorem Ty.whnf_headless {t : Ty} (h : t.view = none) : t.whnf = t := by simp [Ty.whnf, h]

theorem Ty.view_subst_none {t : Ty} (h : t.view = none) (φ : Subst) : (t.subst φ).view = none := by
  rw [Ty.view_subst, h]; rfl

theorem Ty.view_subst_app {t : Ty} {c : Con} {xs : List Ty} (h : t.view = some (.app c xs))
    (φ : Subst) : (t.subst φ).view = some (.app c (xs.map (·.subst φ))) := by
  rw [Ty.view_subst, h]; simp [Ty.view]

/-- A head through substitution: a variable's is its image's, a constructor
stays. -/
theorem Ty.whnf_subst_app {t : Ty} {φ : Subst} {c : Con} {ys : List Ty}
    (h : (t.subst φ).whnf = .app c ys) :
    (∃ a, t.whnf = .var a) ∨ ∃ xs, t.whnf = .app c xs ∧ ys = xs.map (·.subst φ) := by
  rcases Ty.whnf_cases t with ⟨a, ha⟩ | ⟨c', xs, hw, hv⟩ | hv
  · exact .inl ⟨a, ha⟩
  · rw [Ty.whnf_of_view (Ty.view_subst_app hv φ)] at h
    simp only [Ty.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨xs, hw, rfl⟩
  · rw [Ty.whnf_headless (Ty.view_subst_none hv φ)] at h
    have := Ty.view_subst_none hv φ
    rw [h] at this; cases this

theorem Ty.whnf_subst_var {t : Ty} {φ : Subst} {a : Nat} (h : (t.subst φ).whnf = .var a) :
    ∃ b, t.whnf = .var b := by
  rcases Ty.whnf_cases t with ⟨b, hb⟩ | ⟨c', xs, hw, hv⟩ | hv
  · exact ⟨b, hb⟩
  · rw [Ty.whnf_of_view (Ty.view_subst_app hv φ)] at h; cases h
  · rw [Ty.whnf_headless (Ty.view_subst_none hv φ)] at h
    have := Ty.view_subst_none hv φ
    rw [h] at this; cases this

/-- A constructor application's head survives substitution. -/
theorem Ty.whnf_subst_of_app {T : Ty} {c : Con} {xs : List Ty} (h : T.whnf = .app c xs)
    (σ : Subst) : (T.subst σ).whnf = .app c (xs.map (·.subst σ)) := by
  rcases Ty.whnf_cases T with ⟨a, ha⟩ | ⟨c', xs', hw, hv⟩ | hv
  · rw [ha] at h; cases h
  · rw [hw] at h
    simp only [Ty.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Ty.whnf_of_view (Ty.view_subst_app hv σ)
  · rw [Ty.whnf_headless hv] at h
    subst h
    simp [Ty.view] at hv


end Inty
