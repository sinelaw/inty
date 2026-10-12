import Inty.Builtins
import Inty.InferComplete
import Inty.Principal
import Inty.Textbook
import Inty.PolyAnn
import Inty.NoTimeout
import Inty.AssignSub
import Inty.MergeScheme
import Inty.LabelWeaken

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

/-- info: 'Inty.HasTypeS.subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Inty.HasTypeS.subst

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

/-- info: 'Inty.inferProgram_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferProgram_complete

/-- info: 'Inty.HasTypeS.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.HasTypeS.weaken

/-- info: 'Inty.inferInC_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferInC_principal

/-- info: 'Inty.inferProgramC_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferProgramC_principal

/-- info: 'Inty.HasType.toJones' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Inty.HasType.toJones

/-- info: 'Inty.jones_eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.jones_eval_sound

/-- info: 'Inty.jones_never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.jones_never_stuck

/-- info: 'Inty.jones_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.jones_separates

/-- info: 'Inty.infer_complete_polyOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.infer_complete_polyOK

/-- info: 'Inty.inferProgram_complete_polyOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferProgram_complete_polyOK

/-- info: 'Inty.inferProgramC_principal_polyOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inferProgramC_principal_polyOK

/-- info: 'Inty.polyGap_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.polyGap_separates

/-- info: 'Inty.polyId_polyOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.polyId_polyOK

/-- info: 'Inty.eval_noClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.eval_noClock

/-- info: 'Inty.inty_eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inty_eval_sound

/-- info: 'Inty.inty_never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.inty_never_stuck

/-- info: 'Inty.assignSub_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.assignSub_separates

/-- info: 'Inty.funcCheck_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.funcCheck_needed

/-- info: 'Inty.arrCheck_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.arrCheck_needed

/-- info: 'Inty.litStr_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.litStr_needed

/-- info: 'Inty.spreadMerge_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.spreadMerge_typed

/-- info: 'Inty.spreadMerge_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.spreadMerge_needed

/-- info: 'Inty.HasType.extLabels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.HasType.extLabels
