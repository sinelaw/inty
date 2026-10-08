import Inty.Types

/-!
# Type classes

The class instances, mirroring the instance tables in `src/classes`, and
entailment: a constraint holds when it is an instance, or when it is
assumed (a scheme's constraints, while its body is checked). Each class
added to `Cls` gets its instances here, and the soundness proof gets a case
for the operators that use it.
-/

namespace Inty

/-- The instances, as `classes::instances`. -/
inductive Inst : Pred → Prop where
  /-- `Plus Number`. -/
  | plusNumber : Inst ⟨.plus, [.number]⟩
  /-- `Plus String`. -/
  | plusString : Inst ⟨.plus, [.string]⟩

/-- Instances are closed under substitution. -/
theorem Inst.subst (σ : Subst) (h : Inst p) : Inst (p.subst σ) := by
  cases h
  · exact .plusNumber
  · exact .plusString

/-- `p` is an instance, or assumed in `C`. -/
def Entails (C : List Pred) (p : Pred) : Prop := Inst p ∨ p ∈ C

theorem Entails.subst (σ : Subst) (h : Entails C p) :
    Entails (C.map (·.subst σ)) (p.subst σ) :=
  h.elim (fun h => .inl (h.subst σ)) (fun h => .inr (List.mem_map_of_mem h))

/-- Decides `Inst`. -/
def Pred.isInst : Pred → Bool
  | ⟨.plus, [.number]⟩ | ⟨.plus, [.string]⟩ => true
  | _ => false

theorem Pred.isInst_sound {p : Pred} (h : p.isInst = true) : Inst p := by
  obtain ⟨c, args⟩ := p
  cases c
  match args, h with
  | [.number], _ => exact .plusNumber
  | [.string], _ => exact .plusString

/-- Whether some substitution could make `p` an instance: an instance, or a
constraint on a type variable. -/
def Pred.satisfiable : Pred → Bool
  | ⟨.plus, [.var _]⟩ => true
  | p => p.isInst

/-- What a constraint on a type variable defaults to in a typing derivation:
any instance would do, as `Plus a` is satisfied by `Number`. inty leaves
such a constraint in place (`resolve_plus` in `src/builtins`) and accepts
the program, which has a type at every instance. -/
def Pred.defaults : Pred → Subst
  | ⟨.plus, [.var a]⟩ => [(a, .number)]
  | _ => []

/-- The defaults of a list of constraints. -/
def defaultSubst (ps : List Pred) : Subst := ps.flatMap Pred.defaults

theorem Subst.find_mem : ∀ {σ : Subst} {a : Nat} {τ : Ty}, σ.find a = some τ → (a, τ) ∈ σ
  | [], _, _, h => by simp [Subst.find] at h
  | (b, τ') :: σ, a, τ, h => by
    simp only [Subst.find] at h
    split at h
    · cases h; subst_vars; simp
    · exact List.mem_cons_of_mem _ (Subst.find_mem h)

theorem Subst.find_of_mem : ∀ {σ : Subst} {a : Nat} {τ : Ty}, (a, τ) ∈ σ →
    ∃ τ', σ.find a = some τ'
  | [], _, _, h => by cases h
  | (b, τ') :: σ, a, τ, h => by
    simp only [Subst.find]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      rcases List.mem_cons.mp h with h | h
      · cases h; exact absurd rfl hne
      · exact Subst.find_of_mem h

theorem Pred.defaults_mem {p : Pred} {a : Nat} {τ : Ty} (h : (a, τ) ∈ p.defaults) :
    τ = .number := by
  unfold Pred.defaults at h
  split at h <;> simp_all

theorem defaultSubst_find {ps : List Pred} {a : Nat} {τ : Ty}
    (h : (defaultSubst ps).find a = some τ) : τ = .number := by
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp (Subst.find_mem h)
  exact Pred.defaults_mem hp

theorem defaultSubst_mem {ps : List Pred} {a : Nat} (h : (⟨.plus, [.var a]⟩ : Pred) ∈ ps) :
    (defaultSubst ps).find a = some .number := by
  obtain ⟨τ, hτ⟩ := Subst.find_of_mem (σ := defaultSubst ps) (a := a) (τ := .number)
    (List.mem_flatMap.mpr ⟨_, h, by simp [Pred.defaults]⟩)
  rw [hτ, defaultSubst_find hτ]

/-- Defaulting makes every satisfiable constraint an instance. -/
theorem defaultSubst_inst {ps : List Pred} {p : Pred} (hp : p ∈ ps)
    (hs : p.satisfiable = true) : Inst (p.subst (defaultSubst ps)) := by
  obtain ⟨c, args⟩ := p
  cases c
  match args, hs, hp with
  | [.var a], _, hp =>
    simp only [Pred.subst, List.map_cons, List.map_nil, Ty.subst, defaultSubst_mem hp,
      Option.getD_some]
    exact .plusNumber
  | [.number], _, _ => exact .plusNumber
  | [.string], _, _ => exact .plusString

end Inty
