import Init.Data.List
import Cli.Basic
import Lean.Util.SearchPath
import equational_theories.Closure

open Lean Core Elab Cli Closure

def withExtractedResults (imp : Cli.Parsed) (action : Array Entry → DualityRelation → IO Unit) : IO UInt32 := do
  let dualityRelation ← getStoredDualityRelations
  let mut some modules := imp.variableArgsAs? ModuleName |
    imp.printHelp
    return 1
  if modules.isEmpty then
    modules := #[`equational_theories]
  -- Instead of importing modules, read equations from "full_entries.json"
  let jsonStr ← IO.FS.readFile "full_entries.json"
  let json ← match Lean.Json.parse jsonStr with
    | Except.error err => throw $ IO.userError ("Failed to parse JSON: " ++ err)
    | Except.ok j    => pure j
  let rs ← match Lean.FromJson.fromJson? json with
    | Except.error err => throw $ IO.userError ("JSON decode error: " ++ err)
    | Except.ok rs   => pure rs
  action rs dualityRelation
  return 0

def matchFinite (rs : Array Entry) (finite : Bool) : Array Entry :=
  if finite then
    rs.filter (fun r => r.variant matches .implication .. || r.variant matches .facts { finite := true, .. })
  else
    rs.filter (fun r => r.variant matches .implication { finite := false, .. } || r.variant matches .facts .. )

def generateUnknowns (inp : Cli.Parsed) : IO UInt32 := do
  let only_e_c := inp.hasFlag "equivalence_creators"
  let duality := inp.hasFlag "duality"
  let finite_only := inp.hasFlag "finite-only"
  let include_extra := inp.hasFlag "extra"
  if duality && include_extra then
    throw $ IO.userError "Cannot use both --duality and --extra"
  withExtractedResults inp fun rs dualityRelation => do
    let rs := if include_extra then rs else rs.filterMap Entry.keepCore
    let rs := if inp.hasFlag "proven" then rs.filter (·.proven) else rs
    let rs := matchFinite rs finite_only
    let rs := rs.map (·.variant)
    let (components, outcomes) ← Closure.outcomes_mod_equiv rs dualityRelation.dualEquations
    let sortedComponents := components.in_order.qsort (fun a b => Closure.ltEquationNames a[0]! b[0]!)
    let mut unknowns : Array GraphEdge := #[]
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
      let mut allUnknowns : Std.HashSet GraphEdge := {}
      for hi : i in [:components.size] do
        for hj : j in [:components.size] do
          if outcomes[i]![j]!.isNone then
            for lhs in components.in_order[i] do
              for rhs in components.in_order[j] do
                allUnknowns := allUnknowns.insert ⟨lhs, rhs⟩
      let eqsToComponent := components.in_order.map (fun comp => (comp[0]!, comp)) |>.toList |> Std.HashMap.ofList
      let mut unknownsSet : Std.HashSet GraphEdge := {}
      let mut uniqueUnknowns : Array GraphEdge := #[]
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
    "finite-only"; "Only report finite results"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

--- Output of the extract_implications executable.
structure Output where
  implications : Array GraphEdge
  nonimplications : Array GraphEdge

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

def GraphEdge.asJson (v : GraphEdge) : String := s!"\{\"rhs\":\"{v.rhs}\", \"lhs\":\"{v.lhs}\"}"

def Output.asJson (v : Output) : String :=
  s!"\{\"nonimplications\":[{",".intercalate (v.nonimplications.map GraphEdge.asJson).toList}],\"implications\":[{",".intercalate (v.implications.map GraphEdge.asJson).toList}]}"

def generateOutcomes (inp : Cli.Parsed) : IO UInt32 := do
  withExtractedResults inp fun rs dualityRelation => do
    let rs := if inp.hasFlag "extra" then rs else rs.filterMap Entry.keepCore
    let rs := matchFinite rs (inp.hasFlag "finite-only")
    let (equations, outcomes) ← Closure.list_outcomes rs dualityRelation.dualEquations
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
    "finite-only"; "Only report finite results"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"
]

def generateOutput (inp : Cli.Parsed) : IO UInt32 := do
  let include_conj := inp.hasFlag "conjecture"
  let include_impl := inp.hasFlag "closure"
  let finite_only := inp.hasFlag "finite-only"
  let only_implications := inp.hasFlag "only-implications"
  withExtractedResults inp fun rs dualityRelation => do
    let rs := if include_conj then rs else rs.filter (·.proven)
    let rs := matchFinite rs finite_only
    let rs := if only_implications then rs.filter (·.variant matches .implication ..) else rs
    let rs := rs.map (·.variant)
    let rs ← if include_impl then Closure.closure rs dualityRelation.dualEquations else pure (Closure.toEdges rs)
    if inp.hasFlag "json" then
      let implications := (rs.filter (·.isTrue)).map (·.get)
      let nonimplications := (rs.filter (!·.isTrue)).map (·.get)
      IO.println ({implications, nonimplications : Output}).asJson
    else
      for edge in rs do
        if edge.isTrue then IO.println s!"{edge.lhs} → {edge.rhs}"
        else IO.println s!"¬ ({edge.lhs} → {edge.rhs})"

def generateRaw (inp : Cli.Parsed) : IO UInt32 := do
  withExtractedResults inp fun rs _dualityRelation => do
    let rs := matchFinite rs (inp.hasFlag "finite-only")
    if inp.hasFlag "full-entries" then
      IO.println (toJson rs).compress
      return
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
    "finite-only"; "Only report finite results"
    "full-entries"; "Print out the full data for each entry, including source information"

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
    "finite-only"; "Only report finite results"

  ARGS:
    ...files : Array ModuleName; "The files to extract the implications from"

  SUBCOMMANDS: outcomes; unknowns; raw
]

def main (args : List String) : IO UInt32 := do
  extract_implications.validate args
