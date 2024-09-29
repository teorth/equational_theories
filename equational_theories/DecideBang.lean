import Lean

/-!
This is a variant of the `decide` tactic that doesn’t actually check the proposition in meta code.
This is useful in non-interactive mode, where we know it will succeed, and we really just want the
check done once, in the kernel.

This also includes a hack to do large disjunctions outside the `decides`, as inference can blow up.
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
    return proof

private partial def inferDecideFin (p : Expr) : MetaM Expr := do
  let p ← whnfR p
  match p with
  | .forallE i d b bi =>
    match_expr (← whnfR d) with
    | Fin n =>
      let inst ← withLocalDeclD i d fun x => do
        let body := b.instantiate1 x
        let inst ← inferDecideFin body
        mkLambdaFVars #[x] inst
      return mkApp3 (mkConst ``Nat.decidableForallFin) n (.lam i d b bi) inst
    | _ => throwError "Expected Fin n quantifier"
  | _ =>
    match_expr p with
    | True =>
      return mkConst ``True.intro
    | Not p' =>
      let inst ← inferDecideFin p'
      return mkApp2 (mkConst ``instDecidableNot) p' inst
    | Eq t l r =>
      match_expr (← whnfR t) with
      | Fin n =>
        return mkApp3 (mkConst ``instDecidableEqFin) n l r
      | _ => throwError "Expected Fin n equality"
    | _ => throwError "Unsupported proposition {p}"


/-!
Like `decide!`, but only supports goals that are conjunctions of (possibly negations of) goals
of the form `∀ (x … z : Fin n), lhs = rhs`.

Using type class synthesis to infer the decidability instances can be very slow, slower than the
actual proof checking, so this tactic constructs the instances very directly.
-/
elab "decideFin!" : tactic => do
  closeMainGoalUsing `decideFin fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let expectedTypes := splitConjs expectedType
    let proofs ← expectedTypes.mapM fun expectedType => do
      let s ← inferDecideFin expectedType
      let rflPrf ← mkEqRefl (toExpr true)
      return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s rflPrf
    let proof ← proofs.pop.foldrM (mkAppM ``And.intro #[·, ·]) proofs.back
    return proof
