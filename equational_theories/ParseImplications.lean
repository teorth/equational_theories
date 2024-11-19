import Lean.Environment
import Lean.Meta.Basic
import Lean.Util

-- Imports for ensuring names are correct with ``
import equational_theories.FreeMagma
import equational_theories.MagmaLaw
import equational_theories.Preorder

open Lean Qq

/--
`lhs` implies `rhs`, where `lhs` and `rhs` are equation names for the form "Equation17".
-/
structure Implication where
  lhs : String
  rhs : String
  /-- Is this result marked with the Finite typeclass? -/
  finite : Bool
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
  /-- Is this result marked with the Finite typeclass? -/
  finite : Bool
deriving Lean.ToJson, Lean.FromJson, Inhabited

/--
Extracts the equation name out of an expression of the form `EquationN G inst`.
-/
def getEquationName (app : Expr) : Option String := do
  match app with
  | (.app (.app (.const name _) _) _) =>
    -- Copy the string to allow it to safely escape from `Lean.withImportModules`.
    -- Otherwise, segfaults are possible.
    let copy := name.toString
    if copy.startsWith "Equation" then
      some ("" ++ copy)
    else
      none
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
def implicationFromApps (lhs rhs : Expr) (finite : Bool) : Option Implication := do
  let lhsName ← getEquationName lhs
  let rhsName ← getEquationName rhs
  return ⟨lhsName, rhsName, finite⟩

/--
Attempts to parse an `Implication` from the type of a theorem.
-/
def parseImplication (thm_ty : Expr) : MetaM (Option Implication) := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    match fvars with
    | #[g, magma, lhsv] =>parse rhs g magma lhsv false
    | #[g, magma, finite, lhsv] =>
      let (.app (.const `Finite _) _) := ← Meta.inferType finite | return none
      parse rhs g magma lhsv true
    | _ => return none
where
  parse (rhs g magma lhsv : Expr) (finite : Bool) : MetaM (Option Implication) := do
    if !(← Meta.isType g) then return none
    let (.app (.const ``Magma _) _) := ← Meta.inferType magma | return none
    let lhs ← Meta.inferType lhsv
    return implicationFromApps lhs rhs finite

/--
Builds an implication of Laws from the implication of theorems. It should look something like:

```
theorem LawN_implies_LawM : @Law.MagmaLaw.implies.{0} Nat LawN LawM :=
fun (G : Type) (inst : Magma.{0} G) (h : @satisfies.{0, 0} Nat G inst LawN) ↦
  @Iff.mpr (@satisfies.{0, 0} Nat G inst LawM) (@Equation3.{0} G inst) (@LawM.models_iff.{0} G inst)
    (@Subgraph.EquationN_implies_EquationM.{0} G inst
      (@Iff.mp (@satisfies.{0, 0} Nat G inst Law2) (@EquationN.{0} G inst) (@LawN.models_iff.{0} G inst) h))
```
-/
def addLawImplicationThm (thm_ty : Expr) (thm_name : Name) : MetaM Unit := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma, lhsv] := fvars | failure
    if !(← Meta.isType g) then failure
    let (.app (.const ``Magma _) _) := ← Meta.inferType magma | failure
    let lhs ← Meta.inferType lhsv
    let some lhsN := getEquationNumber lhs | failure
    let some rhsN := getEquationNumber rhs | failure
    let some lhsName := getEquationLeanName lhs | failure
    let some rhsName := getEquationLeanName rhs | failure

    -- Build the theorem type
    let lawThmName : Name := Name.mkSimple s!"Law{lhsN}_implies_Law{rhsN}"
    let lhsLawName : Name := Name.mkSimple s!"Law{lhsN}"
    let rhsLawName : Name := Name.mkSimple s!"Law{rhsN}"
    have lhsLaw : Q(Law.NatMagmaLaw) := mkConst lhsLawName
    have rhsLaw : Q(Law.NatMagmaLaw) := mkConst rhsLawName
    let lawThmTy := q($(lhsLaw).implies $rhsLaw)
    have lhsEqn : Q(∀ (G : Type) [Magma G], Prop) := mkConst lhsName [0]
    have rhsEqn : Q(∀ (G : Type) [Magma G], Prop) := mkConst rhsName [0]
    have lhs_models_iff : Q(∀ {G : Type} [Magma G], G ⊧ $lhsLaw ↔ $lhsEqn G) :=
      mkConst (lhsLawName.str "models_iff") [0]
    have rhs_models_iff : Q(∀ {G : Type} [Magma G], G ⊧ $rhsLaw ↔ $rhsEqn G) :=
      mkConst (rhsLawName.str "models_iff") [0]
    have thm : Q(∀ {G : Type} [Magma G], $lhsEqn G → $rhsEqn G) := mkConst thm_name [0]

    let proofTerm : Q($(lhsLaw).implies $rhsLaw) :=
      q(fun _ _ h => ($rhs_models_iff).2 ($thm (($lhs_models_iff).1 h)))

    -- Very important: typecheck the proof before adding it as a theorem!
    Meta.check proofTerm
    let inferredType ← Meta.inferType proofTerm
    Meta.withTransparency .all do
      if ← Meta.isDefEq inferredType lawThmTy then
        -- only adds the theorem if it typechecks!
        let decl := Declaration.thmDecl {
          name := lawThmName,
          levelParams := [],
          type := lawThmTy,
          value := proofTerm
        }
        addDecl decl
      else
        throwError (← Meta.mkHasTypeButIsExpectedMsg inferredType lawThmTy)

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
          match_expr ty1 with
          | Exists b2 body2 =>
            let (.app (.const `Finite _) _) := b2 | return none
            Meta.lambdaTelescope body2 fun _ ty2 => do
              return ← parseList ty2 true
          | _ => return ← parseList ty1 false
      | _ => return none
  | _ => return none
where
  parseList (ty : Expr) (finite : Bool) : MetaM (Option Facts) := do
    let some facts := go #[ty] #[] #[] | return none
    if facts.satisfied.isEmpty && facts.refuted.isEmpty then return none
    if facts.satisfied.isEmpty || facts.refuted.isEmpty then
      Lean.logWarning "Warning: Facts statement has empty satisfied or refuted list"
    return .some { facts with finite := finite }

  -- NB: This is written as a tail-recursive function, else some large facts statements
  -- cause this to blow the stack
  go (todo : Array Expr) (satisfied refuted : Array String) : Option Facts := do
    if todo.isEmpty then
      return ⟨satisfied, refuted, false⟩
    else
      let e := todo.back!
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

/--
Builds an universally quantified implication of Laws from an unconditional Equation theorem.
It should look something like:

```
theorem Subgraph.LawN_implied : ∀ (l : Law.MagmaLaw.{0} Nat), @Law.MagmaLaw.implies.{0} Nat l LawN :=
fun (l : Law.MagmaLaw.{0} Nat) {G : Type} [inst : Magma.{0} G] (a : @satisfies.{0, 0} Nat G inst l) ↦
  @Iff.mpr (@satisfies.{0, 0} Nat G inst Law1) (@Equation1.{0} G inst) (@LawN.models_iff.{0} G inst)
    (@Subgraph.EquationN_true.{0} G inst)
```
-/
def addLawUnconditionalThm (thm_ty : Expr) (thm_name : Name) : MetaM Unit := do
  Meta.forallTelescope thm_ty fun fvars rhs => do
    let #[g, magma] := fvars | failure
    if !(← Meta.isType g) then failure
    let (.app (.const ``Magma _) _) := ← Meta.inferType magma | failure
    let some rhsN := getEquationNumber rhs | failure
    let some rhsName := getEquationLeanName rhs | failure

    -- Build the theorem type
    let lawThmName : Name := Name.mkSimple s!"Anything_implies_Law{rhsN}"
    let rhsLawName : Name := Name.mkSimple s!"Law{rhsN}"
    have rhsLaw : Q(Law.NatMagmaLaw) := mkConst rhsLawName
    let lawThmTy := q(∀ l : Law.NatMagmaLaw, l.implies $rhsLaw)
    have rhsEqn : Q(∀ (G : Type) [Magma G], Prop) := mkConst rhsName [0]
    have rhs_models_iff : Q(∀ {G : Type} [Magma G], G ⊧ $rhsLaw ↔ $rhsEqn G) :=
      mkConst (rhsLawName.str "models_iff") [0]
    have thm : Q(∀ {G : Type} [Magma G], $rhsEqn G) := mkConst thm_name [0]

    let proofTerm : Q(∀ l : Law.NatMagmaLaw, l.implies $rhsLaw) :=
      q(fun _ _ _ _ => ($rhs_models_iff).2 $thm)

    -- Very important: typecheck the proof before adding it as a theorem!
    Meta.check proofTerm
    let inferredType ← Meta.inferType proofTerm
    Meta.withTransparency .all do
      if ← Meta.isDefEq inferredType lawThmTy then
        -- only adds the theorem if it typechecks!
        let decl := Declaration.thmDecl {
          name := lawThmName,
          levelParams := [],
          type := lawThmTy,
          value := proofTerm
        }
        addDecl decl
      else
        throwError (← Meta.mkHasTypeButIsExpectedMsg inferredType lawThmTy)
