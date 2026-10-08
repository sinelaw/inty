import Inty.Builtins
import Inty.InferComplete

/-!
# Axiom audit

The main theorems depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`, or a subset). A `sorry` (`sorryAx`) or any
new axiom changes this output and fails the build.
-/

/-- info: 'Inty.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.eval_sound

/-- info: 'Inty.never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.never_stuck

/-- info: 'Inty.HasType.subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Inty.HasType.subst

/-- info: 'Inty.inferProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferProgram_sound

/-- info: 'Inty.inferProgram_never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferProgram_never_stuck

/-- info: 'Inty.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.eval_mono

/-- info: 'Inty.never_stuck_with_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.never_stuck_with_builtins

/-- info: 'Inty.inferIn_builtins_never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferIn_builtins_never_stuck

/-- info: 'Inty.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.run_mono

/-- info: 'Inty.unify_mgu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.unify_mgu

/-- info: 'Inty.inferIn_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferIn_complete

/-- info: 'Inty.infer_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.infer_complete
