import Lean
import Inty.Statements

/-!
Prints the generated pins of `Inty/Statements.lean` ("The typing rules",
"The interpreter"): run `lake env lean scripts/PrintPins.lean` after
changing a rule or the interpreter, check the change in what it prints,
and paste it over those sections.
-/

open Lean Elab Command

/-- An `example` restating `c`'s type, proved by `c`. -/
def pin (c : Name) : CommandElabM Unit := do
  let some ci := (← getEnv).find? c | throwError "unknown {c}"
  let fmt ← liftTermElabM <| Meta.ppExpr ci.type
  let ty := (toString fmt).replace "\n" "\n    "
  logInfo m!"example : {ty} :=\n  @{c.replacePrefix `Inty .anonymous}\n"

/-- A pin for each rule of an inductive family. -/
elab "#pinRules " n:ident : command => do
  let some (.inductInfo i) := (← getEnv).find? n.getId | throwError "not an inductive"
  i.ctors.forM pin

/-- A pin for each defining equation of a function. -/
elab "#pinEqns " n:ident : command => do
  let some eqs ← liftTermElabM <| Meta.getEqnsFor? n.getId | throwError "no equations"
  eqs.forM pin

set_option pp.fieldNotation false
set_option pp.proofs true
open Inty

#pinRules Inty.HasTypeS
#pinRules Inty.LitTy
#pinRules Inty.UnOpTy
#pinRules Inty.BinOpTyS
#pinRules Inty.ObjCase

#pinEqns Inty.run
#pinEqns Inty.call
#pinEqns Inty.callClosure
#pinEqns Inty.getter
#pinEqns Inty.own
#pinEqns Inty.copyOwn
#pinEqns Inty.runArgs
#pinEqns Inty.runInits
#pinEqns Inty.bindC
#pinEqns Inty.bindArgs
#pinEqns Inty.bindFields
#pinEqns Inty.callEnv
#pinEqns Inty.loopNext
#pinEqns Inty.Value.read
#pinEqns Inty.Value.typeString
#pinEqns Inty.Lit.eval
#pinEqns Inty.UnOp.eval
#pinEqns Inty.BinOp.eval
