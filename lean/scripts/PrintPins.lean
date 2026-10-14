import Lean
import Inty.Builtins
import Inty.InferComplete

/-!
Prints the generated pins of `Inty/Statements.lean` (its section
`Generated`): after changing a rule or the interpreter, run
`python3 scripts/update_pins.py`, which runs this file and puts what it
prints in that section, and check the change in the diff.
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
  let some eqs ← liftTermElabM <| Meta.getEqnsFor? n.getId
    | throwError "no equations"
  eqs.forM pin

/-- How many rules each family has, and equations each function
(`Inty/PinCount.lean`). -/
elab "#pinCounts " fams:ident* " ; " fns:ident* : command => do
  for f in fams do
    let some (.inductInfo i) := (← getEnv).find? f.getId | throwError "not an inductive"
    logInfo m!"#rules {f.getId.replacePrefix `Inty .anonymous} {i.ctors.length}"
  for f in fns do
    let some eqs ← liftTermElabM <| Meta.getEqnsFor? f.getId | throwError "no equations"
    logInfo m!"#equations {f.getId.replacePrefix `Inty .anonymous} {eqs.size}"

set_option pp.fieldNotation false
set_option pp.proofs true
open Inty

#pinRules Inty.HasTypeS
#pinRules Inty.LitTy
#pinRules Inty.UnOpTy
#pinRules Inty.BinOpTyS
#pinRules Inty.ObjCase
#pinRules Inty.Expr.IsValue

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
#pinEqns Inty.BinOp.numeric
#pinEqns Inty.BinOp.compare
#pinEqns Inty.Char.utf16
#pinEqns String.utf16
#pinEqns Inty.unitsLt
#pinEqns Inty.Value.strictEq
-- What the rules' side conditions are made of.
#pinEqns Inty.Expr.writes
#pinEqns Inty.Expr.writesList
#pinEqns Inty.Expr.writesCls
#pinEqns Inty.Annotated
#pinEqns Inty.annMode
#pinEqns Inty.EntailsS
#pinEqns Inty.Ty.whnf
#pinEqns Inty.Ty.dataFields
#pinEqns Inty.Expr.scoped
#pinEqns Inty.Expr.assignsMutable
#pinEqns Inty.Expr.assignsMutableList
#pinEqns Inty.Expr.assignsMutableCls
#pinEqns Inty.Expr.jumpsInLoop
#pinEqns Inty.Expr.jumpsInLoopList
#pinEqns Inty.Value.truthy

#pinCounts Inty.HasTypeS Inty.LitTy Inty.UnOpTy Inty.BinOpTyS Inty.ObjCase Inty.Expr.IsValue ;
  Inty.run Inty.call Inty.callClosure Inty.getter Inty.own Inty.copyOwn Inty.runArgs
  Inty.runInits Inty.bindC Inty.bindArgs Inty.bindFields Inty.callEnv Inty.loopNext Inty.Value.read
  Inty.Value.typeString Inty.Lit.eval Inty.UnOp.eval Inty.BinOp.eval Inty.BinOp.numeric
  Inty.BinOp.compare Inty.Char.utf16 String.utf16 Inty.unitsLt Inty.Value.strictEq Inty.Expr.writes
  Inty.Expr.writesList Inty.Expr.writesCls Inty.Expr.assignsMutable Inty.Expr.assignsMutableList
  Inty.Expr.assignsMutableCls Inty.Expr.jumpsInLoop Inty.Expr.jumpsInLoopList Inty.Value.truthy
  Inty.Annotated Inty.annMode Inty.EntailsS Inty.Ty.whnf Inty.Ty.dataFields Inty.Expr.scoped
