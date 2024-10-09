import Lean.Environment
import Lean.Meta.Basic
import Lean.Util

-- Imports for ensuring names are correct with ``
import equational_theories.FreeMagma
import equational_theories.MagmaLaw

open Lean

/--
`lhs` implies `rhs`, where `lhs` and `rhs` are equation names for the form "Equation17".
-/
structure Implication where
  lhs : String
  rhs : String
deriving Lean.ToJson, Lean.FromJson, DecidableEq, Hashable

/--
Names of equations satisfied rsp. refuted by the same magma; used to concisely express
antiimplications.

For example, if `satisfied = [1, 2]` and `refuted = [4, 5]`, then this expresses
the four antiimplications `¬ 1→4`, `¬ 1→5`, `¬ 2→4`, `¬ 2→5`.
-/
structure Facts where
  satisfied : Array String
  refuted : Array String
deriving Lean.ToJson, Lean.FromJson, Inhabited

/--
Extracts the equation name out of an expression of the form `EquationN G inst`.
-/
def getEquationName (app : Expr) : Option String := do
  match app with
  | (.app (.app (.const name _) _) _) =>
    -- Copy the string to allow it to safely escape from `Lean.withImportModules`.
    -- Otherwise, segfaults are possible.
    some ("" ++ name.toString)
  | _ => none

def getEquationLeanName (app : Expr) : Option Lean.Name := do
  match app with
  | (.app (.app (.const name _) _) _) => some name
  | _ => none

def getEquationNumber (app : Expr) : Option Nat := do
  let nm ← getEquationName app
  nm.replace "Equation" "" |>.toNat?

def isCoreEquationName (s : String) : Bool := Id.run do
  if !s.startsWith "Equation" then return false
  let some n := (s.toSubstring.drop 8).toNat? | return false
  return 0 < n && n <= 4694

def filterCoreEquationName (s : String) : Option String :=
  if isCoreEquationName s then some s else none

/--
Extracts an `Implication` from two expressions of the form `EquationN G inst`.
-/
def implicationFromApps (lhs rhs : Expr) : Option Implication := do
  let lhsName ← getEquationName lhs
  let rhsName ← getEquationName rhs
  return ⟨lhsName, rhsName⟩

/--
Attempts to parse an `Implication` from the type of a theorem.
-/
def parseImplication (thm_ty : Expr) : MetaM (Option Implication) := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma, lhsv] := fvars | return none
    if !(← Meta.isType g) then return none
    let (.app (.const ``Magma _) _) := ← Meta.inferType magma | return none
    let lhs ← Meta.inferType lhsv
    return implicationFromApps lhs rhs

#check mkBVarEx
#check mkBVar

 def addLawImplicationThm (thm_ty : Expr) (thm_name : Name) : MetaM Unit := do
   Meta.forallTelescope thm_ty fun fvars rhs => do
     let #[g, magma, lhsv] := fvars | failure
     if !(← Meta.isType g) then failure
     let (.app (.const ``Magma _) _) := ← Meta.inferType magma | failure
     let lhs ← Meta.inferType lhsv
     let some lhsN := getEquationNumber lhs | failure
     let some rhsN := getEquationNumber rhs | failure

     -- Build the theorem type
     let thmName : Name := Name.mkSimple s!"Law{lhsN}_leq_Law{rhsN}"
     let lhslawName : Name := Name.mkSimple s!"Law{lhsN}"
     let rhslawName : Name := Name.mkSimple s!"Law{rhsN}"
     let lhslaw : Expr := mkConst lhslawName
     let rhslaw : Expr := mkConst rhslawName
     let thmTy : Expr := mkApp3 (mkConst ``LE.le) (mkConst ``Law.NatMagmaLaw) (mkConst lhslawName) (mkConst rhslawName)

     -- Create binders for G and inst
     let gBinder ← Meta.mkFreshExprMVar (Lean.mkSort Lean.levelOne)
     let instBinder ← Meta.mkFreshExprMVar (mkApp (mkConst ``Magma (us:=[Lean.levelZero])) gBinder)
     let satlhs : Expr := mkApp4 (mkConst ``satisfies) (mkConst ``Nat) gBinder instBinder lhslaw
     let hBinder ← Meta.mkFreshExprMVar satlhs

     -- Build expressions in body of proof term (using binders)
     let satrhs : Expr := mkApp4 (mkConst ``satisfies) (mkConst ``Nat) gBinder instBinder rhslaw
     let eqnlhs : Expr := mkApp2 lhs gBinder instBinder
     let eqnrhs : Expr := mkApp2 rhs gBinder instBinder
     let lhs_models_iff : Expr := mkApp2 (mkConst <| Name.str lhslawName "models_iff") gBinder instBinder
     let rhs_models_iff : Expr := mkApp2 (mkConst <| Name.str rhslawName "models_iff") gBinder instBinder

     -- Build the implication
     let impl : Expr := mkApp3 (mkConst thm_name) gBinder instBinder
       (mkApp4 (mkConst ``Iff.mp) hBinder eqnlhs lhs_models_iff gBinder)

     -- Build the final proof term
     let proofTerm : Expr := --Meta.mkLambdaFVars #[gBinder, instBinder, hBinder] <|
          mkLambda `G BinderInfo.implicit gBinder <|
          mkLambda `inst BinderInfo.instImplicit instBinder <|
          mkLambda `h BinderInfo.default hBinder <|
          mkApp5 (mkConst ``Iff.mpr) satrhs eqnrhs rhs_models_iff impl gBinder

     -- Wrap the proof term in forallE expressions
     let wrappedProofTerm ← Meta.mkForallFVars #[gBinder, instBinder] proofTerm

     logInfo "built term : checking"
     -- Very important: typecheck the proof before adding it as a theorem!
     Meta.check wrappedProofTerm
     logInfo "proof term type correct"

     let inferredType ← Meta.inferType wrappedProofTerm
     logInfo "type inferred"
     if ← Meta.isDefEq inferredType thmTy then
        -- only adds the theorem if it typechecks!
        let decl := Declaration.thmDecl {
          name := thmName,
          levelParams := [],
          type := thmTy,
          value := wrappedProofTerm
        }
        addDecl decl

     else
       throwError (← Meta.mkHasTypeButIsExpectedMsg inferredType thmTy)
/-
LE.le.{0} Law.NatMagmaLaw (Law.MagmaLaw.instLE Nat) Law2 Law3 :=
fun {G : Type} [inst : Magma.{0} G]
(h : satisfies Nat G inst Law2) =>
Iff.mpr (satisfies Nat G inst Law3) (Equation3.{0} G inst) (Law3.models_iff G inst)
(Subgraph.Equation2_implies_Equation3.{0} G inst (Iff.mp (satisfies Nat G inst Law2)
(Equation2.{0} G inst) (Law2.models_iff G inst) h))
-/


/--
Attempts to parse an exisential statement of monoid facts from the type of a theorem.
-/
partial def parseFacts (thm_ty : Expr) : MetaM (Option Facts) := do
  match_expr thm_ty with
  | Exists b body =>
    if !(← Meta.isType b) then return none
    Meta.lambdaTelescope body fun fvars ty => do
      let #[g] := fvars | return none
      if !(← Meta.isType g) then return none
      match_expr ty with
      | Exists b1 body1 =>
        let (.app (.const `Magma _) _) := b1 | return none
        Meta.lambdaTelescope body1 fun fvars1 ty1 => do
          let #[magma] := fvars1 | return none
          let (.app (.const `Magma _) _) := ← Meta.inferType magma | return none
          let some facts := go #[ty1] #[] #[] | return none
          if facts.satisfied.isEmpty && facts.refuted.isEmpty then return none
          return .some facts
      | _ => return none
  | _ => return none
where
  -- NB: This is written as a tail-recursive function, else some large facts statements
  -- cause this to blow the stack
  go (todo : Array Expr) (satisfied refuted : Array String) : Option Facts := do
    if todo.isEmpty then
      return ⟨satisfied, refuted⟩
    else
      let e := todo.back
      let todo := todo.pop
      if e.isAppOfArity ``And 2 then
        go ((todo.push e.appFn!.appArg!).push e.appArg!) satisfied refuted
      else if e.isAppOfArity ``Not 1 then
        let name ← getEquationName e.appArg!
        go todo satisfied (refuted.push name)
      else
        let name ← getEquationName e
        go todo (satisfied.push name) refuted

/--
Attempts to parse theorem type as an unconditional equation.
-/
def parseUnconditionalEquation (thm_ty : Expr) : MetaM (Option String) := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma] := fvars | return none
    if !(← Meta.isType g) then return none
    let (.app (.const `Magma _) _) := ← Meta.inferType magma | return none
    return getEquationName rhs
