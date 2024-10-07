import Batteries.Data.Array.Basic
import Batteries.Tactic.Lint.Frontend
import Cli.Basic
import Lean.Util.SearchPath
import equational_theories.Closure

open Lean Core Elab Cli

def withExtractedResults (imp : Cli.Parsed) (action : Array Entry → IO Unit) : IO UInt32 := do
  let mut some modules := imp.variableArgsAs? ModuleName |
    imp.printHelp
    return 1
  if modules.isEmpty then
    modules := #[`equational_theories]
  searchPathRef.set compile_time_search_path%

  unsafe withImportModules (modules.map ({module := ·})) {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
      let rs ← Result.extractEquationalResults
      action rs
      pure 0

structure DualityRelation where
  dualEquations : Std.HashMap String String

def DualityRelation.ofFile (path : String) : IO DualityRelation := do
  let dualsJson := Json.parse (←IO.FS.readFile path) |>.toOption.get!
  let mut dualEquations : Std.HashMap String String := {}
  for pair in dualsJson.getArr?.toOption.get! do
    let a := s!"Equation{pair.getArr?.toOption.get![0]!.getNat?.toOption.get!}"
    let b := s!"Equation{pair.getArr?.toOption.get![1]!.getNat?.toOption.get!}"
    dualEquations := dualEquations.insert a b
    dualEquations := dualEquations.insert b a
  pure ⟨dualEquations⟩

def DualityRelation.dual (rel : DualityRelation) (imp : Implication) : Option Implication :=
  if isCoreEquationName imp.lhs && isCoreEquationName imp.rhs then
    some ⟨rel.dualEquations.getD imp.lhs imp.lhs, rel.dualEquations.getD imp.rhs imp.rhs⟩
  else
    none

def generateUnknowns (inp : Cli.Parsed) : IO UInt32 := do
  let only_e_c := inp.hasFlag "equivalence_creators"
  let duality := inp.hasFlag "duality"
  let include_extra := inp.hasFlag "extra"
  if duality && include_extra then
    throw $ IO.userError "Cannot use both --duality and --extra"
  withExtractedResults inp fun rs => do
    let rs := if include_extra then rs else rs.filterMap Entry.keepCore
    let rs := if inp.hasFlag "proven" then rs.filter (·.proven) else rs
    let rs := rs.map (·.variant)
    let (components, outcomes) ← Closure.outcomes_mod_equiv rs
    let sortedComponents := components.in_order.qsort (fun a b => Closure.ltEquationNames a[0]! b[0]!)
    let mut unknowns : Array Implication := #[]
    for c1 in sortedComponents do
      let i := components[c1]!
      for c2 in sortedComponents do
        let j := components[c2]!
        if outcomes[i]![j]!.isNone then
          if only_e_c then
            if outcomes[j]![i]!.getD false then
              unknowns := unknowns.push ⟨c1[0]!, c2[0]!⟩
          else
            unknowns := unknowns.push ⟨c1[0]!, c2[0]!⟩
    if duality then
      let dualityRelation ← DualityRelation.ofFile "data/duals.json"
      let mut allUnknowns : Std.HashSet Implication := {}
      for hi : i in [:components.size] do
        for hj : j in [:components.size] do
          if outcomes[i]![j]!.isNone then
            for lhs in components.in_order[i] do
              for rhs in components.in_order[j] do
                allUnknowns := allUnknowns.insert ⟨lhs, rhs⟩
      let eqsToComponent := components.in_order.map (fun comp => (comp[0]!, comp)) |>.toList |> Std.HashMap.ofList
      let mut unknownsSet : Std.HashSet Implication := {}
      let mut uniqueUnknowns : Array Implication := #[]
      for imp in unknowns do
        match dualityRelation.dual imp with
          | none => throw $ IO.userError "No dual found"
          | some dualImp =>
            if allUnknowns.contains dualImp then
              unless unknownsSet.contains dualImp do
                uniqueUnknowns := uniqueUnknowns.push imp
              for l_eq in eqsToComponent[imp.lhs]! do
                for r_eq in eqsToComponent[imp.rhs]! do
                  unknownsSet := unknownsSet.insert ⟨l_eq, r_eq⟩
      unknowns := uniqueUnknowns
    IO.println (toJson unknowns).compress

def unknowns : Cmd := `[Cli|
  unknowns VIA generateUnknowns;
  "List all unknown implications modulo equivalence."

  FLAGS:
    proven; "Only consider proven results"
    equivalence_creators; "Output only implications whose converse is known to be true"
    extra; "Include extra equations that are not in the core set"
    duality; "Only include one implication of each dual pair"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

--- Output of the extract_implications executable.
structure Output where
  implications : Array Implication
  nonimplications : Array Implication

--- Output of the extract_implications outcomes subcommand.
structure OutputOutcomes where
  equations : Array String
  outcomes : Array (Array Closure.Outcome)
  deriving Lean.ToJson

--- Output of the extract_implications raw subcommand.
structure OutputRaw where
  implications : Array Implication
  facts : Array Facts
  unconditionals : Array String
deriving Lean.ToJson, Lean.FromJson

def Implication.asJson (v : Implication) : String := s!"\{\"rhs\":\"{v.rhs}\", \"lhs\":\"{v.lhs}\"}"

def Output.asJson (v : Output) : String :=
  s!"\{\"nonimplications\":[{",".intercalate (v.nonimplications.map Implication.asJson).toList}],\"implications\":[{",".intercalate (v.implications.map Implication.asJson).toList}]}"

def generateOutcomes (inp : Cli.Parsed) : IO UInt32 := do
  withExtractedResults inp fun rs => do
    let rs := if inp.hasFlag "extra" then rs else rs.filterMap Entry.keepCore
    let (equations, outcomes) ← Closure.list_outcomes rs
    if inp.hasFlag "hist" then
      let mut count : Std.HashMap Closure.Outcome Nat := {}
      for a in outcomes do
        for b in a do
          count := count.insert b (count.getD b 0 + 1)
      let hist := Json.mkObj $ count.toList.map fun (x, n) => (toString x, toJson n)
      IO.println hist.pretty
    else
      IO.println (toJson ({equations, outcomes : OutputOutcomes})).compress

def outcomes : Cmd := `[Cli|
  outcomes VIA generateOutcomes;
  "Output the status of all implications."

  FLAGS:
    hist; "Create a histogram instead of outputting all outcomes"
    extra; "Include extra equations that are not in the core set"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def generateOutput (inp : Cli.Parsed) : IO UInt32 := do
  let include_conj := inp.hasFlag "conjecture"
  let include_impl := inp.hasFlag "closure"
  let only_implications := inp.hasFlag "only-implications"
  withExtractedResults inp fun rs => do
    let rs := if include_conj then rs else rs.filter (·.proven)
    let rs := if only_implications then rs.filter (·.variant matches .implication ..) else rs
    let rs := rs.map (·.variant)
    let rs ← if include_impl then Closure.closure rs else pure (Closure.toEdges rs)
    if inp.hasFlag "json" then
      let implications := (rs.filter (·.isTrue)).map (·.get)
      let nonimplications := (rs.filter (!·.isTrue)).map (·.get)
      IO.println ({implications, nonimplications : Output}).asJson
    else
      for edge in rs do
        if edge.isTrue then IO.println s!"{edge.lhs} → {edge.rhs}"
        else IO.println s!"¬ ({edge.lhs} → {edge.rhs})"

def generateRaw (inp : Cli.Parsed) : IO UInt32 := do
  withExtractedResults inp fun rs => do
    let rs := if inp.hasFlag "proven" then rs.filter (·.proven) else rs
    let mut implications : Array Implication := #[]
    let mut facts : Array Facts := #[]
    let mut unconditionals : Array String := #[]
    for entry in rs do
      match entry.variant with
      | .implication imp => implications := implications.push imp
      | .facts fact => facts := facts.push fact
      | .unconditional s => unconditionals := unconditionals.push s
    let output : OutputRaw := ⟨implications, facts, unconditionals⟩
    IO.println (toJson output).pretty

def raw : Cmd := `[Cli|
  raw VIA generateRaw;
  "Print all equational results in JSON format for use in other scripts."

  FLAGS:
    proven; "Only consider proven results"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def extract_implications : Cmd := `[Cli|
  extract_implications VIA generateOutput;
  "Extract the implications shown in the mentioned files."

  FLAGS:
    «conjecture»; "Include conjectures"
    closure; "Compute the transitive closure"
    json; "Output the data as JSON"
    "only-implications"; "Only consider implications"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"

  SUBCOMMANDS: outcomes; unknowns; raw
]

def main (args : List String) : IO UInt32 := do
  extract_implications.validate args
