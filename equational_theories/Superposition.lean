import Lean
import Batteries.Tactic.Exact
import Qq

open Lean Elab Command Term Meta Qq

def Lean.MVarId.congrPre' (mvarId : MVarId) (eqs : List Expr) : MetaM Unit := do
  let mvarId ← mvarId.heqOfEq
  try mvarId.refl; return catch _ => pure ()
  try mvarId.hrefl; return catch _ => pure ()
  for eq in eqs do
    try mvarId.assignIfDefeq eq; return catch _ => pure ()
  throwError "Couldn't assign"

partial def Lean.MVarId.congrWith (mvarId_ : MVarId) (eqs : List Expr) : MetaM Unit :=
  go [mvarId_] eqs
  where
  go (mvarId_ : List MVarId) (eqs : List Expr) : MetaM Unit := do
    match mvarId_ with
    | [] => pure ()
    | mvarId :: todo =>
      let s ← saveState
      try mvarId.refl; go todo eqs; return catch _ => s.restore
      for eq in eqs do
        try mvarId.assignIfDefeq eq; go todo eqs; return catch _ => s.restore
      go (todo ++ (← mvarId.congrCore)) eqs

def Lean.Expr.eqswap (e : Expr) : Expr := Id.run do
  if let some (typ, lhs, rhs) := e.eq? then
    return mkAppN e.getAppFn #[typ, rhs, lhs]
  if let some (typ, lhs, rhs) := e.ne? then
    return mkAppN e.getAppFn #[typ, rhs, lhs]
  return e

def mkEqNeSymm (h : Expr) : MetaM Expr := do
  if (← inferType h).isAppOf ``Eq then
    return ← mkEqSymm h
  if (← inferType h).isAppOf ``Ne then
    return ← mkAppM ``Ne.symm #[h]
  throwError "Nope!"

elab "superpose " eq1:term:arg eq2:term:arg : term <= typ => do
  let eq1 ← elabTerm eq1 none
  let eq1type ← inferType eq1
  let eq2 ← elabTerm eq2 none
  let eq2type ← inferType eq2
  let (args1, _, _e1) ← forallMetaTelescope eq1type
  let eq1 := mkAppN eq1 args1
  let (args2, _, e2) ← forallMetaTelescope eq2type
  let eq2 := mkAppN eq2 args2
  let s ← saveState
  try
    let v ← mkFreshExprMVar (← mkEq e2 typ)
    let m := v.mvarId!
    -- logInfo m!"Consider {v} using {eq1}"
    m.congrWith [eq1, (← mkEqSymm eq1)]
    let expr ← instantiateMVars (← mkEqMP v eq2)
    guard (← isDefEq typ (← inferType expr))
    for mvar in ← getMVarsNoDelayed expr do
      mvar.assumption
    return expr
  catch _ =>
    restoreState s
    let v ← mkFreshExprMVar (← mkEq e2.eqswap typ)
    let m := v.mvarId!
    m.congrWith [eq1, (← mkEqSymm eq1)]
    let expr ← instantiateMVars (← mkEqMP v (← mkEqNeSymm eq2))
    guard (← isDefEq typ (← inferType expr))
    for mvar in ← getMVarsNoDelayed expr do
      mvar.assumption
    return expr


elab "subsumption " eq1:term:arg eq2:term:arg : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let eq1 ← elabTerm eq1 none
    let eq1type ← inferType eq1
    let eq2 ← elabTerm eq2 none
    let eq2type ← inferType eq2
    let (args1, _, e1) ← forallMetaTelescope eq1type
    let eq1 := mkAppN eq1 args1
    let (args2, _, e2) ← forallMetaTelescope eq2type
    let eq2 := mkAppN eq2 args2
    let s ← saveState
    guard (e1.isAppOfArity ``Ne 3)
    try
      guard (← isDefEq (← mkEq (e1.getArg! 1) (e1.getArg! 2)) e2)
      let expr := .app eq1 eq2
      guard (← isDefEq goalType (← inferType expr))
      let expr ← instantiateMVars expr
      for mvar in ← getMVarsNoDelayed expr do
        mvar.assumption
      goal.assign expr
    catch _ =>
      restoreState s
      guard (← isDefEq (← mkEq (e1.getArg! 1) (e1.getArg! 2)) e2.eqswap)
      let expr := .app eq1 (← mkEqSymm eq2)
      guard (← isDefEq goalType (← inferType expr))
      let expr ← instantiateMVars expr
      for mvar in ← getMVarsNoDelayed expr do
        mvar.assumption
      goal.assign expr

macro "mod_symm " ar:term:arg : term => `(by first | exact $ar | exact Eq.symm $ar | exact Ne.symm $ar)
