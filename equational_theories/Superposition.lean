import Lean
import Batteries.Tactic.Exact
import Qq

open Lean Elab Command Term Meta Qq

theorem Eq.comm'.{u} {α : Sort u} {a b : α} : (a = b) = (b = a) := propext Eq.comm

theorem Ne.comm'.{u} {α : Sort u} {a b : α} : (a ≠ b) = (b ≠ a) := propext ne_comm

partial def Lean.MVarId.congrWith (mvarId_ : MVarId) (eqs : List Expr) : MetaM Unit :=
  go [mvarId_] eqs true
  where
  go (mvarId_ : List MVarId) (eqs : List Expr) (try_symm : Bool := true) : MetaM Unit := do
    match mvarId_ with
    | [] => pure ()
    | mvarId :: todo =>
      let s ← saveState
      try mvarId.refl; go todo eqs true; return catch _ => s.restore
      for eq in eqs do
        try mvarId.assignIfDefeq eq; go todo eqs true; return catch _ => s.restore
      try
        go (todo ++ (← mvarId.congrCore)) eqs true
      catch e =>
        if try_symm then
          let ttype : Q(Prop) ← mvarId.getType
          match ttype with
          | ~q(($a = $b) = ($c = $d)) =>
            s.restore
            let nmv ← mkFreshExprMVarQ q(($b = $a) = ($c = $d))
            mvarId.assignIfDefeq (q(Eq.trans Eq.comm' $nmv) : Q(($a = $b) = ($c = $d)))
            go (nmv.mvarId! :: todo) eqs false
          | ~q(($a ≠ $b) = ($c ≠ $d)) =>
            s.restore
            let nmv ← mkFreshExprMVarQ q(($b ≠ $a) = ($c ≠ $d))
            mvarId.assignIfDefeq (q(Eq.trans Ne.comm' $nmv) : Q(($a ≠ $b) = ($c ≠ $d)))
            go (nmv.mvarId! :: todo) eqs false
          | _ => throw e
        else throw e

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
  let v ← mkFreshExprMVar (← mkEq e2 typ)
  let m := v.mvarId!
  m.congrWith [eq1, (← mkEqSymm eq1)]
  let expr ← instantiateMVars (← mkEqMP v eq2)
  guard (← isDefEq typ (← inferType expr))
  for mvar in ← getMVarsNoDelayed expr do
    mvar.assumption
  return expr

partial def doSubsumptionSingle {α : Type} (t1 : Q(Prop)) (target : Q(Prop))
    (cont : Q($t1 → $target) → MetaM α) : MetaM α := do
  let s ← saveState
  match target with
  | ~q($l ∨ $r) =>
    try
      have := (← assertDefEqQ q($l) q($t1)).down
      cont q(fun h ↦ Or.inl h)
    catch _ =>
      restoreState s
      match q($l) with
      | ~q($l1 = $l2) =>
        try
          have := (← assertDefEqQ q($l2 = $l1) q($t1)).down
          cont q(fun h ↦ Or.inl h.symm)
        catch _ =>
          restoreState s
          doSubsumptionSingle t1 q($r) fun x ↦ cont q(fun h ↦ .inr ($x h))
      | ~q($l1 ≠ $l2) =>
        try
          have := (← assertDefEqQ q($l2 ≠ $l1) q($t1)).down
          cont q(fun h ↦ Or.inl h.symm)
        catch _ =>
          restoreState s
          doSubsumptionSingle t1 q($r) fun x ↦ cont q(fun h ↦ .inr ($x h))
      | _ =>
        doSubsumptionSingle t1 q($r) fun x ↦ cont q(fun h ↦ .inr ($x h))
  | _ =>
    try
      have := (← assertDefEqQ q($target) q($t1)).down
      cont q(id)
    catch e =>
      restoreState s
      match q($target) with
      | ~q($l1 = $l2) =>
        have := (← assertDefEqQ q($l2 = $l1) q($t1)).down
        cont q(Eq.symm)
      | ~q($l1 ≠ $l2) =>
        have := (← assertDefEqQ q($l2 ≠ $l1) q($t1)).down
        cont q(Ne.symm)
      | _ => throw e

partial def doSubsumptionWith {α : Type} (res : Q(Prop)) (t2 : Q(Prop)) (target : Q(Prop))
    (cont : Q(¬$res → $t2 → $target) → MetaM α) :
    MetaM α := do
  match t2 with
  | ~q($l ∨ $r) =>
    let s ← saveState
    try
      have := (← assertDefEqQ q($res) q($l)).down
      doSubsumptionWith res q($r) target fun resR ↦
        cont q(fun r h ↦ h.elim (fun nh ↦ (r nh).elim) ($resR r))
    catch _ =>
      restoreState s
      doSubsumptionSingle q($l) target fun hl ↦
        doSubsumptionWith res q($r) target fun resR ↦
          cont q(fun r h ↦ h.elim $hl ($resR r))
  | _ =>
    let s ← saveState
    try
      have := (← assertDefEqQ q($res) q($t2)).down
      cont q(fun r h ↦ (r h).elim)
    catch _ =>
      restoreState s
      doSubsumptionSingle t2 target fun x ↦ cont q(fun _ ↦ $x)

partial def doResolutionSingle {α : Type} (t1 : Q(Prop)) (t2 : Q(Prop)) (e2 : Q($t2)) (target : Q(Prop))
    (can_resolution : Bool) (cont : Q($t1 → $target) → Bool → MetaM α) : MetaM α := do
  match t1 with
  | ~q(¬ $t3) =>
    if can_resolution then
      let s ← saveState
      try
        doSubsumptionSingle t1 target fun x ↦ cont x true
      catch _ =>
        restoreState s
        match q($t3) with
        | ~q($l = $r) =>
          try
            doSubsumptionWith t3 t2 target fun ss ↦ cont q(fun h ↦ $ss h $e2) false
          catch _ =>
            restoreState s
            doSubsumptionWith q($r = $l) t2 target fun ss ↦ cont q(fun h ↦ $ss (Ne.symm h) $e2) false
        | _ => doSubsumptionWith t3 t2 target fun ss ↦ cont q(fun h ↦ $ss h $e2) false
    else doSubsumptionSingle t1 target fun x ↦ cont x can_resolution
  | _ => doSubsumptionSingle t1 target fun x ↦ cont x can_resolution

partial def doResolution (t1 : Q(Prop)) (t2 : Q(Prop)) (e2 : Q($t2)) (target : Q(Prop))
    (can_resolution : Bool) : MetaM Q($t1 → $target) := do
  match t1 with
  | ~q($l ∨ $r) =>
    doResolutionSingle q($l) t2 e2 target can_resolution (fun hl new_can_resolution ↦ do
      let resR ← doResolution q($r) t2 e2 target new_can_resolution
      return q(fun h ↦ h.elim $hl $resR)
    )
  | _ =>
    doResolutionSingle t1 t2 e2 target can_resolution (fun x _ ↦ pure x)


elab "resolve " eq1:term:arg eq2:term:arg : term <= typ => do
  let eq1 ← elabTerm eq1 none
  let eq1type ← inferType eq1
  let eq2 ← elabTerm eq2 none
  let eq2type ← inferType eq2
  let (args1, _, e1) ← forallMetaTelescope eq1type
  let eq1 := mkAppN eq1 args1
  let (args2, _, e2) ← forallMetaTelescope eq2type
  let eq2 := mkAppN eq2 args2
  let s ← saveState
  try
    return .app (← doResolution e1 e2 eq2 typ true) eq1
  catch _ =>
    s.restore
    return .app (← doResolution e2 e1 eq1 typ true) eq2

elab "subsumption " eq1:term:arg eq2:term:arg : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let eq1 ← elabTerm eq1 none
    let eq1type ← inferType eq1
    let eq2 ← elabTerm eq2 none
    let eq2type ← inferType eq2
    let mut (args1, _, _e1) ← forallMetaTelescopeReducing eq1type
    let mut eq1 := mkAppN eq1 args1
    let mut (args2, _, _e2) ← forallMetaTelescopeReducing eq2type
    let mut eq2 := mkAppN eq2 args2
    unless ← isDefEq _e1 goalType do
      ⟨eq1, eq2, args1, args2⟩ := (eq2, eq1, args2, args1)
      guard (← isDefEq _e2 goalType)
    let s ← saveState
    try
      guard (← isDefEq args1.back! eq2)
      let expr ← instantiateMVars eq1
      for mvar in ← getMVarsNoDelayed expr do
        mvar.assumption
      goal.assign expr
    catch _ =>
      restoreState s
      guard (← isDefEq args1.back! (← mkEqSymm eq2))
      let expr ← instantiateMVars eq1
      for mvar in ← getMVarsNoDelayed expr do
        mvar.assumption
      goal.assign expr

macro "mod_symm " ar:term:arg : term => `(by first | exact $ar | exact Eq.symm $ar | exact Ne.symm $ar)
