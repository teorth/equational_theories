import Lean

/-!
This is a variant of the `decide` tactic that doesn’t actually check the proposition in meta code.
This is useful in non-interactive mode, where we know it will succeed, and we really just want the
check done once, in the kernel.

This also includes a hack to do large disjunctions outside the `decdies`, as inference can blow up.
-/

open Lean Elab Tactic Meta

private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

private def splitConjs (e : Lean.Expr) : Array (Lean.Expr) := Id.run do
  let mut e := e
  let mut r := #[]
  while e.isAppOf `And do
    r := r.push e.appFn!.appArg!
    e := e.appArg!
  r := r.push e
  return r

elab "decide!" : tactic => do
  closeMainGoalUsing `decide fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let expectedTypes := splitConjs expectedType
    let proofs ← expectedTypes.mapM fun expectedType => do
      let d ← mkDecide expectedType
      let d ← instantiateMVars d
      -- Get instance from `d`
      let s := d.appArg!
      let rflPrf ← mkEqRefl (toExpr true)
      return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s rflPrf
    let proof ← proofs.pop.foldrM (mkAppM ``And.intro #[·, ·]) proofs.back
    check proof
    return proof
