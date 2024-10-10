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
  ⟨(List ·), _, inferInstance, ``instLiftingMagmaFamilyList⟩,
  ⟨(Multiset ·), _, inferInstance, ``instLiftingMagmaFamilyMultiset⟩,
  ⟨(Id ·), _, instLiftingMagmaFamilyLeftProj, ``instLiftingMagmaFamilyLeftProj⟩,
  ⟨(Id ·), _, instLiftingMagmaFamilyRightProj, ``instLiftingMagmaFamilyRightProj⟩
]

def generateNonimplications (inst : LiftingMagmaFamilyInstance) : CoreM Unit := do
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
  let eqnThms ← Result.extractEquationalResults
  let closure ← Closure.closure <| eqnThms.map Entry.variant
  let mut output := "import equational_theories.LiftingMagmaFamilies\n"
  for (posLawName) in positives do
    for (negLawName) in negatives do
      let posEqnName := Name.mkSimple <| magmaLawNameToEquationName posLawName.toString
      let negEqnName := Name.mkSimple <| magmaLawNameToEquationName negLawName.toString
      let thm := Closure.Edge.nonimplication { lhs := posEqnName.toString, rhs := posEqnName.toString }
      unless closure.contains thm do
        let resultName := Name.mkSimple <| s!"{posEqnName.toString}_not_implies_{negEqnName.toString}"
        -- let counterExample : TSyntax `command ← `(command|
        --   @[equational_result]
        --   theorem $(mkIdent resultName) : ∃ (G : Type _) (_ : Magma G), $(mkIdent posEqnName) G ∧ $(mkIdent negEqnName) G :=
        --     @proveNonimplication _ _ $(mkIdent inst.instName) _ _ _ _ $(mkIdent (posLawName ++ `models_iff)) $(mkIdent (negLawName ++ `models_iff))
        --     (by decide) (by decide))
        output := output ++ s!"\n@[equational_result]\ntheorem {resultName} : ∃ (G : Type _) (_ : Magma G), {posEqnName} G ∧ {negEqnName} G :=
          @proveNonimplication _ _ {inst.instName} _ _ _ _ {posLawName ++ `models_iff} {negLawName ++ `models_iff} (by decide) (by decide)"
    let filePath : System.FilePath := "." / "equational_theories" / "Generated" /
      "InvariantMetatheoremNonimplications" / s!"{inst.instName}_counterexamples.lean"
    IO.FS.writeFile filePath output

def generateAllNonimplications : CoreM Unit := do
  for inst in liftingMagmaFamilyInstances do
    generateNonimplications inst

def main : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let env ← importModules #[
    { module := `equational_theories.Equations },
    { module := `equational_theories.AllEquations }] .empty
  EIO.toIO (fun _ ↦ IO.userError "Failed to generate counterexample files.") <|
            generateAllNonimplications.run' { fileName := "", fileMap := default } { env := env }
