import Lean

/-!
This is a variant of the `decide` tactic that doesn’t actually check the proposition in meta code.
This is useful in non-interactive mode, where we know it will succeed, and we really just want the
check done once, in the kernel.
-/

open Lean Elab Tactic Meta

private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

elab "decide!" : tactic => do
  closeMainGoalUsing `decide fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let d ← mkDecide expectedType
    let d ← instantiateMVars d
    -- Get instance from `d`
    let s := d.appArg!
    let rflPrf ← mkEqRefl (toExpr true)
    return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s rflPrf
