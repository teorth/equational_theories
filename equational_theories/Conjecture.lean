import Lean.Elab.Exception
import Lean.Elab.Declaration

import equational_theories.ParseImplications

open Lean Parser Elab Command

namespace Conjecture

/--
Like `proof_wanted` from Batteries, but records the conjecture in an
environment extension.
-/
@[command_parser]
def «conjecture» := leading_parser
  declModifiers false >> "conjecture" >> declId >> ppIndent declSig

/-- An entry in the conjecture environment extension.
-/
inductive EntryVariant where
  | implication : Implication → EntryVariant
  | nonimplication : Implication → EntryVariant
  | other : EntryVariant

/-- An entry in the conjecture environment extension -/
structure Entry where
/-- Name of the declaration. -/
(name : Name)
/-- Lean code to be included in the extracted problem file. -/
(variant : EntryVariant)

initialize conjectureExtension : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `conjecture
    addImportedFn := Array.concatMap id
    addEntryFn    := Array.push
  }

/-- Elaborates a `conjecture` declaration. The declaration is translated to an axiom during
elaboration, but it's then removed from the environment.
-/
@[command_elab «conjecture»]
def elabConjecture : CommandElab
  | `($mods:declModifiers conjecture $name $args* : $res) => do
    let maybe_entry ← withoutModifyingEnv do
      let modifiers ← elabModifiers mods
      let expanded_decl_id ← expandDeclId name modifiers

      -- The helper axiom is used instead of `sorry` to avoid spurious warnings
      elabDeclaration <| ← `(command| axiom helper (p : Prop) : p)
      elabDeclaration <| ← `(command| $mods:declModifiers
                                      theorem $name $args* : $res := helper _)

      match ← getConstInfo expanded_decl_id.declName with
      | .thmInfo  (val : TheoremVal) =>
        liftCoreM <| Meta.MetaM.run' do
        if let some imp ← parseImplication val.type then
          return some ⟨val.name, .implication imp⟩
        if let some nimp ← parseNonimplication val.type then
          return some ⟨val.name, .nonimplication nimp⟩
        return some ⟨val.name, .other⟩
      | _ => pure none

    if let some entry := maybe_entry then
      modifyEnv fun env =>
        conjectureExtension.addEntry env entry
    pure ()
  | _ => throwUnsupportedSyntax

/-- Returns the contents of the conjecture environment extension.
-/
def extractConjectures {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return conjectureExtension.getState (← getEnv)

/-- Prints the contents of the conjecture environment extension.
-/
syntax (name := printConjectures) "#print_conjectures" : command

elab_rules : command
| `(command| #print_conjectures) => do
  let cs ← extractConjectures
  for ⟨name, conj⟩ in cs do
    match conj with
    | .implication ⟨lhs, rhs⟩ => println! "{name}: {lhs} → {rhs}"
    | .nonimplication ⟨lhs, rhs⟩ => println! "{name}: ¬ ({lhs} → {rhs})"
    | _ => println! "{name}"
