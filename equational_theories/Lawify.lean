import equational_theories.MagmaLaw
import Lean
import Batteries.Tactic.Exact
import Qq

open Lean Elab Command Term Meta Qq

open FreeMagma Law

partial def collectVaribles (law : Expr) : MetaM (Array Expr) :=
  go law {}
  where
  go (law : Expr) (hm : Array Expr) : MetaM (Array Expr) := do
    match ← whnf law with
    | .app (.app (.app (.const ``MagmaLaw.mk _) _) l1) l2
    | .app (.app (.app (.const ``Fork _) _) l1) l2 =>
      go l2 (← go l1 hm)
    | .app (.app (.const ``Leaf _) _) l1 =>
      return bif ← hm.anyM (isDefEq · l1) then hm else hm.push l1
    | _ => throwError m!"Non-concrete law: {law}"

def toName (n : Nat) : Name :=
  .mkSimple (if n < 6 then ("xyzwuv".get ⟨n⟩).toString else s!"extra{n}")

partial def match_law_equation (G : Q(Type)) (law : Expr) (eq : Expr) (law_vars : Array Expr) (eq_vars : Array Expr) :
    MetaM Unit := do
  let law ← whnf law
  let eq ← whnf eq
  if !law.isMVar then
    match ← whnf law with
    | .app (.app (.app (.const ``MagmaLaw.mk _) _) l1) l2 =>
      let left : Q($G) ← mkFreshExprMVar G
      let right : Q($G) ← mkFreshExprMVar G
      unless (← isDefEq eq q($left = $right)) do throwError m!"Type {eq} doesn't match {law}"
      match_law_equation G l1 left law_vars eq_vars
      match_law_equation G l2 right law_vars eq_vars
    | .app (.app (.app (.const ``Fork _) _) l1) l2 =>
      let left ← mkFreshExprMVar G
      let right ← mkFreshExprMVar G
      unless (← isDefEq eq (← mkAppM ``Magma.op #[left, right])) do throwError m!"Type {eq} doesn't match {law}"
      match_law_equation G l1 left law_vars eq_vars
      match_law_equation G l2 right law_vars eq_vars
    | .app (.app (.const ``Leaf _) _) l1 =>
      let some ind ← law_vars.findIdxM? (isDefEq · l1) | throwError "This shouldn't be possible."
      unless (← isDefEq eq eq_vars[ind]!) do throwError m!"Type {eq} doesn't match {law}"
    | _ => throwError m!"Non-concrete law: {law}"
    return
  match ← whnf eq with
  | .app (.app (.app (.const ``Eq _) _) l1) l2 =>
    let left : Q(FreeMagma Nat) ← mkFreshExprMVar q(FreeMagma Nat)
    let right : Q(FreeMagma Nat) ← mkFreshExprMVar q(FreeMagma Nat)
    unless (← isDefEq law q(MagmaLaw.mk $left $right)) do throwError m!"Type {eq} doesn't match {law}"
    match_law_equation G left l1 law_vars eq_vars
    match_law_equation G right l2 law_vars eq_vars
  | .app (.app (.proj ``Magma 0 _) l1) l2
  | .app (.app (.app (.app (.const ``Magma.op _) _) _) l1) l2 =>
    let left ← mkFreshExprMVar q(FreeMagma Nat)
    let right ← mkFreshExprMVar q(FreeMagma Nat)
    unless (← isDefEq law (← mkAppM ``Fork #[left, right])) do throwError m!"Type {eq} doesn't match {law}"
    match_law_equation G left l1 law_vars eq_vars
    match_law_equation G right l2 law_vars eq_vars
  | x =>
    let some ind ← eq_vars.findIdxM? (isDefEq · x) |
      throwError m!"Invalid value in equation {x}."
    unless (← isDefEq law law_vars[ind]!) do throwError m!"Type {eq} doesn't match {law}"

/--
Convert an equation to a law
-/
elab "equation_to_law " eq:term:arg : term <= typ => do
  let G : Q(Type) ← mkFreshExprMVar none
  let _inst : Q(Magma $G) ← mkFreshExprMVar q(Magma $G)
  let law_α : Q(Type) ← mkFreshExprMVar none
  let law : Q(MagmaLaw $law_α) ← mkFreshExprMVar q(MagmaLaw $law_α)
  unless ← isDefEq typ q($G ⊧ $law) do
    throwError m!"Type {typ} is not an application of satisfies"
  let G ← instantiateMVars G
  let law ← instantiateMVars law
  let retype ← withNewMCtxDepth do
    let vars : Array Expr ← collectVaribles law
    withLocalDeclsD ((Array.range vars.size).map (fun x ↦ (toName x, fun _ ↦ pure G))) fun ld ↦ do
      let retype ← mkFreshExprMVar (some (.sort .zero))
      match_law_equation G law retype vars ld
      instantiateMVars (← mkForallFVars ld retype)
  let eq ← elabTerm eq retype
  forallTelescopeReducing typ fun targs ttype ↦ do
  let (eqargs, _, eqtype) ← forallMetaTelescopeReducing retype
  unless (← isDefEq (← instantiateMVars ttype) (← instantiateMVars eqtype)) do throwError m!"Type {ttype} doesn't match {eqtype}"
  return ← mkLambdaFVars targs (mkAppN eq eqargs)

/--
Convert a law to an equation
-/
elab "law_to_equation " lawTerm:term:arg : term <= typ => do
  let (targs, _, ttype) ← forallMetaTelescopeReducing typ
  if targs.isEmpty then
    throwError m!"Equation {typ} doesn't have any variables!"
  let G : Q(Type) ← inferType targs[0]!
  let _inst : Q(Magma $G) ← synthInstanceQ q(Magma $G)
  let law : Q(MagmaLaw ℕ) ← withNewMCtxDepth do
    let law ← mkFreshExprMVarQ q(MagmaLaw Nat)
    let lawVars := (Array.range targs.size).map (fun n : Nat ↦ q(FreeMagma.Leaf $n))
    match_law_equation G law ttype lawVars targs
    instantiateMVars law
  let lawTerm : Q($G ⊧ $law) ← elabTerm lawTerm q($G ⊧ $law)
  let arr : Q(List $G) ← mkListLit G targs.toList
  let default : Q($G) := targs[0]!
  return ← instantiateMVars (← mkLambdaFVars targs q($lawTerm fun x : Nat ↦ ($arr).getD x $default))

macro "equation_to_law" : tactic => `(tactic| refine equation_to_law ?_)

macro "law_to_equation" : tactic => `(tactic| refine law_to_equation ?_)

example (G : Type) [Magma G] (h : Equation7 G) : G ⊧ (Lf 0 ≃ (Lf 2 ⋆ Lf 1)) := by
  equation_to_law
  exact h

example (G : Type) [Magma G] (h : G ⊧ (Lf 0 ≃ (Lf 1 ⋆ Lf 0))) : ∀ a b : G, a = b ◇ a := by
  law_to_equation
  exact h
