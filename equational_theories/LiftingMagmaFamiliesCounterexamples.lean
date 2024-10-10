import equational_theories.LiftingMagmaFamilies
import equational_theories.EquationsCommand
import equational_theories.Closure
import equational_theories.Equations
import equational_theories.AllEquations

open Law
open Lean Elab Command Term

-- TODO: Automatically generate these structures when a lifting magma family is defined
structure LiftingMagmaFamilyInstance where
  G : (α : Type) → [DecidableEq α] → Type
  instDecidableEq : ∀ α [DecidableEq α], Magma (G α)
  instLiftingMagmaFamily : LiftingMagmaFamily G
  instName : Name

def liftingMagmaFamilyInstances : Array LiftingMagmaFamilyInstance := #[
  ⟨(List ·), _, instLiftingMagmaFamilyList, ``instLiftingMagmaFamilyList⟩,
  ⟨(Multiset ·), _, instLiftingMagmaFamilyMultiset, ``instLiftingMagmaFamilyMultiset⟩,
  ⟨(Id ·), _, instLiftingMagmaFamilyLeftProj, ``instLiftingMagmaFamilyLeftProj⟩,
  ⟨(Id ·), _, instLiftingMagmaFamilyRightProj, ``instLiftingMagmaFamilyRightProj⟩
]

-- the non-implications from the environment are cached in a special datastructure for faster lookup
def generateNonImplicationsTable : CoreM (Std.HashMap String (Array String)) := do
  let eqnThms ← Result.extractEquationalResults
  let closure ← Closure.closure <| eqnThms.map Entry.variant
  let nonImplications := closure.filterMap fun
    | .implication _ => none
    | .nonimplication e => some e
  return nonImplications.foldl (init := {}) fun map ⟨lhs, rhs⟩ ↦
    match map[lhs]? with
    | some arr => map.insert lhs (arr.push rhs)
    | none => map.insert lhs #[rhs]

def containsImplication (table : Std.HashMap String (Array String)) (implication : Implication) : Bool :=
  match table[implication.lhs]? with
   | some arr => arr.contains implication.rhs
   | none => false

def generateInvariantMetatheoremResults (inst : LiftingMagmaFamilyInstance) (nonImplications : Std.HashMap String (Array String)) : CoreM Unit := do
  let laws ← getMagmaLaws
  let mut positives : Array Name := #[]
  let mut negatives : Array Name := #[]
  for (lawName, law) in laws do
    -- using `Lean.reduceBool` for a speed-up
    let result := Lean.reduceBool <| @decide _ <|
      @instDecidableSatisfies Nat inst.G inst.instDecidableEq inst.instLiftingMagmaFamily _ law
    if result then
      positives := positives.push lawName
    else
      negatives := negatives.push lawName
  let mut output := "import equational_theories.LiftingMagmaFamilies\nimport equational_theories.EquationalResult\nimport equational_theories.AllEquations\n\n"
  for (posLawName) in positives do
    for (negLawName) in negatives do
      let posEqnName := Name.mkSimple <| magmaLawNameToEquationName posLawName.toString
      let negEqnName := Name.mkSimple <| magmaLawNameToEquationName negLawName.toString
      unless containsImplication nonImplications { lhs := posEqnName.toString, rhs := posEqnName.toString } do
        let resultName := Name.mkSimple <| s!"{posEqnName.toString}_not_implies_{negEqnName.toString}"
        -- let counterExample : TSyntax `command ← `(command|
        --   @[equational_result]
        --   theorem $(mkIdent resultName) : ∃ (G : Type _) (_ : Magma G), $(mkIdent posEqnName) G ∧ $(mkIdent negEqnName) G :=
        --     @proveNonimplication _ _ $(mkIdent inst.instName) _ _ _ _ $(mkIdent (posLawName ++ `models_iff)) $(mkIdent (negLawName ++ `models_iff))
        --     (by decide) (by decide))
        output := output ++ s!"\n\n@[equational_result]\nconjecture {resultName} : ∃ (G : Type _) (_ : Magma G), {posEqnName} G ∧ ¬{negEqnName} G"
  let filePath : System.FilePath := "." / "equational_theories" / "Generated" /
      "InvariantMetatheoremNonimplications" / s!"{inst.instName}_counterexamples.lean"
  IO.FS.writeFile filePath output

def generateAllNonimplications : CoreM Unit := do
  for inst in liftingMagmaFamilyInstances do
    generateInvariantMetatheoremResults inst (← generateNonImplicationsTable)

def main : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let env ← importModules #[
    { module := `equational_theories },
    { module := `equational_theories.Equations },
    { module := `equational_theories.AllEquations }] .empty
  EIO.toIO (fun _ ↦ IO.userError "Failed to generate counterexample files.") <|
            generateAllNonimplications.run' { fileName := "", fileMap := default } { env := env }
