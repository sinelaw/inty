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

end Inty
