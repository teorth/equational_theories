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
  /-- An equation that always holds. -/
  | unconditional : String → EntryVariant
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
       let entry ← match info with
                   | .thmInfo  (val : TheoremVal) =>
                     if let some imp ← parseImplication val.type then
                       pure <| ⟨val.name, filename, .implication imp⟩
                     else if let some nimp ← parseNonimplication val.type then
                       pure <| ⟨val.name, filename, .nonimplication nimp⟩
                     else if let some uncond ← parseUnconditionalEquation val.type then
                       pure <| ⟨val.name, filename, .unconditional uncond⟩
                     else
                       throwError "failed to match type of @[equational_result] theorem"
                   | _ => throwError "@[equational_result] is only allowed on theorems"
       modifyEnv fun env =>
         equationalResultsExtension.addEntry env entry
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
    | .unconditional rhs => println! "{name}: {rhs} holds unconditionally"

--- Output of the extract_implications executable.
structure Output where
  implications : Array Implication
  nonimplications : Array Implication
  unconditionals : Array String
deriving Lean.ToJson, Lean.FromJson

def collectResults {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m Output := do
  let rs := equationalResultsExtension.getState (← getEnv)
  let mut implications : Array Implication := #[]
  let mut nonimplications : Array Implication := #[]
  let mut unconditionals : Array String := #[]
  for ⟨_name, _filename, res⟩ in rs do
    match res with
    | .implication imp => implications := implications.push imp
    | .nonimplication nimp => nonimplications := nonimplications.push nimp
    | .unconditional s => unconditionals := unconditionals.push s
  return ⟨implications, nonimplications, unconditionals⟩
