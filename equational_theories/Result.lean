import Lean.Elab.Exception
import Lean.Elab.Declaration

import equational_theories.ParseImplications

open Lean Parser Elab Command

namespace Result

/-- An entry in the equational results environment extension.
-/
inductive EntryVariant where
  | implication : Implication → EntryVariant
  | nonimplication : Implication → EntryVariant
deriving Lean.ToJson, Lean.FromJson

/-- An entry in the equational results environment extension -/
structure Entry where
/-- Name of the declaration. -/
(name : Name)
/-- Name of the file where this declaration was found. -/
(filename : String)
/-- Which kind of result is it? -/
(variant : EntryVariant)
deriving Lean.ToJson, Lean.FromJson

initialize equationalResultsExtension : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `equational_result
    addImportedFn := Array.concatMap id
    addEntryFn    := Array.push
  }

private def equationalResultHelpString : String :=
"tags theorems that provide implications or negated implications to the directed graph"

/-- Initialization of `equational_result` attribute -/
initialize equationalResultAttr : Unit ←
  registerBuiltinAttribute {
    name  := `equational_result
    descr := equationalResultHelpString
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx _attrKind => do
       let filename := (←read).fileName
       discard <| Meta.MetaM.run do
       let info ← getConstInfo declName
       let maybe_entry ← match info with
                    | .thmInfo  (val : TheoremVal) =>
                      if let some imp ← parseImplication val.type then
                        pure <| some ⟨val.name, filename, .implication imp⟩
                      else if let some nimp ← parseNonimplication val.type then
                        pure <| some ⟨val.name, filename, .nonimplication nimp⟩
                      else
                        pure none
                    | _ => pure none
       if let some entry := maybe_entry then
         modifyEnv fun env =>
           equationalResultsExtension.addEntry env entry
       pure ()
    erase := fun _declName =>
      throwError "can't remove `equational_result` attribute (not implemented yet)"
  }


/-- Returns the contents of the equational results environment extension.
-/
def extractEquationalResults {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return equationalResultsExtension.getState (← getEnv)

/-- Prints the contents of the equational results environment extension.
-/
syntax (name := printEquationalResults) "#print_equational_results" : command

elab_rules : command
| `(command| #print_equational_results) => do
  let rs ← extractEquationalResults
  for ⟨name, _filename, res⟩ in rs do
    match res with
    | .implication ⟨lhs, rhs⟩ => println! "{name}: {lhs} → {rhs}"
    | .nonimplication ⟨lhs, rhs⟩ => println! "{name}: ¬ ({lhs} → {rhs})"

--- Output of the extract_implications executable.
structure Output where
  implications : List Implication
  nonimplications : List Implication
deriving Lean.ToJson, Lean.FromJson

def collectResults {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m Output := do
  let rs := equationalResultsExtension.getState (← getEnv)
  let mut implications : List Implication := []
  let mut nonimplications : List Implication := []
  for ⟨_name, _filename, res⟩ in rs do
    match res with
    | .implication imp => implications := imp::implications
    | .nonimplication nimp => nonimplications := nimp::nonimplications
  return ⟨implications, nonimplications⟩
