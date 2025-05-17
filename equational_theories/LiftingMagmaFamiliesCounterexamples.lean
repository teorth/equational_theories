import equational_theories.LiftingMagmaFamilies
import equational_theories.Closure
import equational_theories.Equations.All
open Law
open Lean Elab Command Term

-- TODO: Automatically generate these structures when a lifting magma family is defined
structure LiftingMagmaFamilyInstance where
  G : Type → Type
  instDecidableEq : ∀ α [DecidableEq α], Magma (G α)
  instLiftingMagmaFamily : LiftingMagmaFamily G
  instName : Name

def liftingMagmaFamilyInstances : Array LiftingMagmaFamilyInstance := #[
  ⟨List, inferInstance, instLiftingMagmaFamilyList, ``instLiftingMagmaFamilyList⟩,
  ⟨Multiset, instMagmaMultiset, instLiftingMagmaFamilyMultiset, ``instLiftingMagmaFamilyMultiset⟩,
  ⟨LeftProj, inferInstance, instLiftingMagmaFamilyLeftProj, ``instLiftingMagmaFamilyLeftProj⟩,
  ⟨RightProj, inferInstance, instLiftingMagmaFamilyRightProj, ``instLiftingMagmaFamilyRightProj⟩,
  ⟨Finset, instMagmaFinset, instLiftingMagmaFamilyFinset, ``instLiftingMagmaFamilyFinset⟩
]

def Std.HashMap.push {α β} [BEq α] [Hashable α] (map : Std.HashMap α (Array β)) (a : α) (b : β) : Std.HashMap α (Array β) :=
  match map[a]? with
  | some arr => map.insert a (arr.push b)
  | none => map.insert a #[b]

-- the non-implications from the environment are cached in a special datastructure for faster lookup
def generateNonImplicationsTable : CoreM (Std.HashMap String (Array String) × Std.HashMap String (Array String)) := do
  let eqnThms ← Result.extractEquationalResults
  IO.println s!"Extracted {eqnThms.size} equational results. Generating their closure ..."
  let closure ← Closure.closure (eqnThms.map Entry.variant) (← Closure.getStoredDualityRelations).dualEquations
  IO.println s!"Generated the closure of size {closure.size} ..."
  return closure.foldl (init := (.emptyWithCapacity (capacity := 8192), .emptyWithCapacity (capacity := 8192))) fun (implMap, nonImplMap) edge ↦
    match edge with
    | .implication ⟨lhs, rhs⟩ =>
      (implMap.push lhs rhs, nonImplMap)
    | .nonimplication ⟨lhs, rhs⟩ =>
      (implMap, nonImplMap.push lhs rhs)

def generateInvariantMetatheoremResults (inst : LiftingMagmaFamilyInstance)
    (implications nonImplications : Std.HashMap String (Array String)) (laws : Array (Name × NatMagmaLaw))
    (path : System.FilePath) : CoreM Unit := do
  let mut positives : Array Name := #[]
  let mut negatives : Array Name := #[]
  let mut nonImplications := nonImplications
  for (lawName, law) in laws do
    let result := @decide _ <|
      @instDecidableSatisfiesLaw Nat inst.G inst.instLiftingMagmaFamily _ law
    if result then
      positives := positives.push lawName
    else
      negatives := negatives.push lawName
  IO.println s!"Filtered laws into {positives.size} positives and {negatives.size} negatives ..."
  let mut output := "import equational_theories.LiftingMagmaFamilies\nimport equational_theories.EquationalResult\nimport equational_theories.Equations.All"
  for posLawName in positives do
    let posEqnName := magmaLawNameToEquationName posLawName.toString
    let establishedNonConclusions := nonImplications[posEqnName]?.getD #[]
    for negLawName in negatives do
      let negEqnName := magmaLawNameToEquationName negLawName.toString
      unless establishedNonConclusions.contains negEqnName do
        output := output ++ generateEquationResult posEqnName negEqnName inst.instName
        let establishedConclusions := implications[posEqnName]?.getD #[]
        for posImplName in establishedConclusions do
          nonImplications := nonImplications.push posImplName negEqnName
  IO.println "Writing to file ..."
  IO.FS.writeFile path output
where
  generateEquationResult (pos neg : String) (instName : Name) : String :=
    s!"\n\n@[equational_result]\ntheorem {pos}_not_implies_{neg} : ∃ (G : Type) (_ : Magma G), {pos} G ∧ ¬ {neg} G :=
    LiftingMagmaFamily.establishNonimplication (family := {instName}) _ {equationNameToMagmaLawName pos}.models_iff {equationNameToMagmaLawName neg}.models_iff"

def outputDir : System.FilePath := "." / "equational_theories" / "Generated"

def generateAllNonimplications : CoreM Unit := do
  IO.println "Generating table of existing non-implications ..."
  let (implTable, nonImplTable) ← generateNonImplicationsTable
  IO.println s!"Generated tables of implications and non-implications, retrieving laws ..."
  let laws ← getMagmaLaws
  IO.println s!"Retrieved {laws.size} laws from the environment ..."
  for inst in liftingMagmaFamilyInstances do
    IO.println s!"Generating non-implications for {inst.instName} ..."
    generateInvariantMetatheoremResults inst implTable nonImplTable laws <|
      outputDir / "InvariantMetatheoremNonimplications" / s!"{inst.instName}_counterexamples.lean"
  let mainFile := liftingMagmaFamilyInstances.foldl (init := "") fun acc inst ↦
    acc ++ s!"import equational_theories.Generated.InvariantMetatheoremNonimplications.{inst.instName}_counterexamples\n"
  IO.FS.writeFile (outputDir / "InvariantMetatheoremNonimplications.lean") mainFile

def main : IO Unit := do
  -- this is to prevent previously generated results from accidentally shadowing the new ones
  IO.println "Erasing previously generated files..."
  for inst in liftingMagmaFamilyInstances do
    IO.FS.writeFile (outputDir / "InvariantMetatheoremNonimplications" / s!"{inst.instName}_counterexamples.lean") ""
  IO.println "Generating counterexample files..."
  IO.println "Loading environment..."
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `equational_theories },
    { module := `equational_theories.Equations.All }] .empty
  EIO.toIO (fun _ ↦ IO.userError "Failed to generate counterexample files.") <|
            generateAllNonimplications.run' { fileName := "", fileMap := default } { env := env }
