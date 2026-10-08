import Inty.Soundness

/-!
# Axiom audit

The main theorems depend only on Lean's standard classical axioms. A `sorry`
(`sorryAx`) or any new axiom changes this output and fails the build.
-/

/-- info: 'Inty.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.eval_sound

/-- info: 'Inty.never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Inty.never_stuck
