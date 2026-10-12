import Inty.Textbook
import Inty.InferComplete

/-!
# inty's assignment rule

inty subsumes an assignment's value into the variable's type
(`infer_assign`): `x = e` stores a value of any type that injects into
`x`'s, as `/** let x: Number | null */ let x = null; x = 5;` does. The rule
`HasTypeS.assignCheck` says so: `e` is checked against `x`'s type, which
has no type variables. It is on in a system with `Sys.assignSub`, and off
in `HasType`'s, whose inference it would make incomplete: where inference
still has a type variable for `x`'s type, it can't tell which values
inject into it. So the differential test's front end (`Inty.Wire`) writes
an assignment to an annotated `let` as `x = (const t: T = e; t)`, which
`HasType` types alike.

`Sys.inty` is the system with the rule (`HasTypeI`), and soundness covers it
directly, without that rewrite:

* every typing of `HasType` is one of `HasTypeI` (`HasType.toInty`);
* `HasTypeI` is sound (`inty_eval_sound`, `inty_never_stuck`);
* it types `x = 5` for a `Nullable number` variable, which `HasType` and
  inference don't (`assignSub_separates`).
-/

namespace Inty

/-- The system with inty's assignment rule. -/
def Sys.inty : Sys := { Sys.narrow with assignSub := true }

/-- Typing with inty's assignment rule. -/
abbrev HasTypeI := HasTypeS Sys.inty

theorem Sys.inty_narrowLike : Sys.inty.NarrowLike := ⟨rfl, rfl⟩

theorem Sys.narrow_le_inty : Sys.narrow.Le Sys.inty := ⟨id, id, rfl, id, fun _ => rfl⟩

/-- Every typing of `HasType` is one with inty's assignment rule. -/
theorem HasType.toInty {L : List String} {C : List Pred} {Γ : Ctx} {R : Option Ty} {rm md : Mode}
    {e : Expr} {τ : Ty} (h : HasType L C Γ R rm md e τ) : HasTypeI L C Γ R rm md e τ :=
  h.mono Sys.narrow_le_inty

/-- Soundness with inty's assignment rule. -/
theorem inty_eval_sound (clock : Nat) (ht : HasTypeI L C Γ R rm md e τ) (hC : HoldsOrVar C)
    (hG : G W (Γ.map Scheme.toW) env) (hH : HeapOK clock W h) : Safe (run clock env h e) clock W τ R :=
  eval_soundW clock (ht.toWideOf Sys.inty_narrowLike) hC.toW hG hH

/-- A closed program typed with inty's assignment rule never gets stuck. -/
theorem inty_never_stuck (ht : HasTypeI L C [] none rm md e τ) (hC : HoldsOrVar C) (clock : Nat)
    (s : Stuck) : eval clock [] [] e ≠ .stuck s :=
  never_stuckW (ht.toWideOf Sys.inty_narrowLike) hC.toW clock s

/-! ## The separating program -/

/-- `Number | null`, an annotation. -/
def nullableNumber : Scheme := ⟨0, .app (.maybe .null) [.app .number []], []⟩

/-- `/** let x: Number | null */ let x = null; x = 5; x`. -/
def assignSubExample : Expr :=
  .let_ true (some nullableNumber) (.lit .null) (.seq (.assign 0 (.lit (.number 5))) (.var 0))

theorem assignSubExample_typed :
    HasTypeI L [] [] none .synth .synth assignSubExample (.maybe .null .number) := by
  have hT : (Ty.maybe .null .number).ftv = [] := rfl
  have hv : HasTypeI L [] [nullableNumber] none .synth .synth (.var 0) (.maybe .null .number) := by
    exact HasTypeS.var (S := Sys.inty) (C := []) (R := none) (rm := .synth)
      (Γ := [nullableNumber]) (i := 0) (τs := []) rfl rfl (by simp [Scheme.instPreds, nullableNumber])
  refine .let_ nullableNumber [] (fun m _ => ?_) (.inl ⟨rfl, rfl⟩)
    (.inr fun _ h => by simp [nullableNumber] at h) (fun a h => by cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (.seq (.drop (.assignCheck rfl rfl rfl rfl (TyEq.refl _) hT
      (.inj (.lit .number) hT (.inl (Inst.instEq (.injectSome (TyEq.refl _) hT rfl
        (by decide) (by decide))))))) hv)
  show HasTypeI L [] [] none .synth .check (.lit .null) (.maybe .null .number)
  exact .inj (.lit .null) hT (.inl (Inst.instEq (.injectNothing (TyEq.refl _) hT)))

/-- Inference rejects it, as written: the front end's rewrite is what it
accepts. -/
theorem assignSubExample_rejected : inferProgram assignSubExample = none := by decide +kernel

/-- So `HasType` doesn't type it: inference is complete for it. -/
theorem assignSubExample_untyped : ¬ HasType [] [] [] none .synth .synth assignSubExample τ := fun h => by
  obtain ⟨_, hτ, -⟩ := inferProgram_complete (e := assignSubExample) (by decide +kernel)
    (by decide +kernel) h
  rw [assignSubExample_rejected] at hτ
  cases hτ

/-- inty's assignment rule types strictly more than `HasType`. -/
theorem assignSub_separates :
    HasTypeI [] [] [] none .synth .synth assignSubExample (.maybe .null .number) ∧
      ∀ τ, ¬ HasType [] [] [] none .synth .synth assignSubExample τ :=
  ⟨assignSubExample_typed, fun _ => assignSubExample_untyped⟩

end Inty
