import Lean.Elab.Exception
import Lean.Elab.Declaration

import equational_theories.ParseImplications

/-!
This file defines the @[equational_result] attribute, intended for marking theorems that
represent edges in the implication graph.

At one point we discussed getting the same information by scanning through the environment
and collecting all theorems that have the correct shape.
See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Refactoring.20the.20Lean.20file.20structure/near/473148427.

That approach would have the advantage of allowing the theorems to be more succinct in the
source code (no need to add an attribute). However, using an attribute and environment
extension, as done in this file, has the following advantages:
  - If a theorem does not quite match the correct shape, the attribute handler can report
    the error immediately at the theorem declaration.
  - Recording the results just once avoids the need to linearly scan the whole environment
    (could get expensive) at each downstream usage point.
  - Requiring explicit opt-in prevents the possibilty of accidental inclusions of unwanted theorems.
-/

open Lean Parser Elab Command

namespace Result

/-- An entry in the equational results environment extension.
-/
inductive EntryVariant where
  | implication : Implication → EntryVariant
  | facts : Facts → EntryVariant
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
                     else if let some facts ← parseFacts val.type then
                       pure <| ⟨val.name, filename, .facts facts⟩
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
    | .facts ⟨satisfied, refuted⟩ => println! "{name}: {satisfied} // {refuted}"
    | .unconditional rhs => println! "{name}: {rhs} holds unconditionally"

--- Output of the extract_implications executable.
structure Output where
  implications : Array Implication
  facts : Array Facts
  unconditionals : Array String
deriving Lean.ToJson, Lean.FromJson

def collectResults {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m Output := do
  let rs := equationalResultsExtension.getState (← getEnv)
  let mut implications : Array Implication := #[]
  let mut facts : Array Facts := #[]
  let mut unconditionals : Array String := #[]
  for ⟨_name, _filename, res⟩ in rs do
    match res with
    | .implication imp => implications := implications.push imp
    | .facts fact => facts := facts.push fact
    | .unconditional s => unconditionals := unconditionals.push s
  return ⟨implications, facts, unconditionals⟩
