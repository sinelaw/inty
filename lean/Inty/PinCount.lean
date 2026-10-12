import Lean

/-!
# Counting rules and equations

`#rules F k` fails unless the inductive family `F` has `k` rules, and
`#equations f k` unless the function `f` has `k` defining equations: the
pinned statements (`Inty/Statements.lean`) restate each rule and equation,
and these catch one added.
-/

namespace Inty.PinCount

open Lean Elab Command Meta

elab "#rules " n:ident k:num : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some (.inductInfo i) := (← getEnv).find? c | throwError "{c} isn't an inductive family"
  unless i.ctors.length == k.getNat do
    throwError "{c} has {i.ctors.length} rules, the pinned statements {k.getNat}"

elab "#equations " n:ident k:num : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some eqs ← liftTermElabM <| getEqnsFor? c | throwError "{c} has no equations"
  unless eqs.size == k.getNat do
    throwError "{c} has {eqs.size} equations, the pinned statements {k.getNat}"

end Inty.PinCount
