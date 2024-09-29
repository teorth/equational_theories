import Lean.Elab.Exception
import Lean.Elab.Declaration

import equational_theories.ParseImplications

open Lean Parser Elab Command

namespace Result

syntax (name := result) declModifiers "result " declId ppIndent(declSig) declVal : command

/-- An entry in the conjecture environment extension.
-/
inductive EntryVariant where
  | implication : Implication → EntryVariant
  | nonimplication : Implication → EntryVariant
  deriving DecidableEq

/-- An entry in the conjecture environment extension -/
structure Entry where
/-- Name of the declaration. -/
(name : Name)

/-- Name of the file where this declaration was found. -/
(filename : String)

/-- Lean code to be included in the extracted problem file. -/
(variant : EntryVariant)

initialize resultExtension : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `result
    addImportedFn := Array.concatMap id
    addEntryFn    := Array.push
  }

/-- Elaborates a `result` declaration.
-/
elab_rules : command
| `(command| $dm:declModifiers result%$rs $di:declId $ds:declSig $dv:declVal) => do
  let filename := (←read).fileName
  let modifiers ← elabModifiers dm
  let expanded_decl_id ← expandDeclId di modifiers

  let cmd ← `(command | $dm:declModifiers theorem $di $ds $dv)
  Lean.Elab.Command.elabCommand cmd

  let maybe_entry ← match ←getConstInfo expanded_decl_id.declName with
                    | .thmInfo  (val : TheoremVal) =>
                      liftCoreM <| Meta.MetaM.run' do
                      if let some imp ← parseImplication val.type then
                        return some ⟨val.name, filename, .implication imp⟩
                      if let some nimp ← parseNonimplication val.type then
                        return some ⟨val.name, filename, .nonimplication nimp⟩
                      return  none
                    | _ => pure none

  if let some entry := maybe_entry then
    modifyEnv fun env =>
      resultExtension.addEntry env entry

  pure ()

/-- Returns the contents of the result environment extension.
-/
def extractResults {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return resultExtension.getState (← getEnv)

/-- Prints the contents of the conjecture environment extension.
-/
syntax (name := printResults) "#print_results" : command

elab_rules : command
| `(command| #print_results) => do
  let rs ← extractResults
  for ⟨name, _filename, res⟩ in rs do
    match res with
    | .implication ⟨lhs, rhs⟩ => println! "{name}: {lhs} → {rhs}"
    | .nonimplication ⟨lhs, rhs⟩ => println! "{name}: ¬ ({lhs} → {rhs})"
