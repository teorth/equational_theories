import Lean
import equational_theories.Magma

open Lean Elab Command

/--
For a more concise syntax, but more importantly to speed up elaboration (where type inference
for each `∘` makes processing this file very slow) we defined custom syntax for defining
equations, and a custom elaborator that instantiates the instante parameter of `∘`.
-/
elab tk:"equation " i:num " := " t:term : command => do
  let G := mkIdent (← MonadQuotation.addMacroScope `G)
  let inst := mkIdent (← MonadQuotation.addMacroScope `inst)
  let eqName := mkIdent (.mkSimple s!"Equation{i.getNat}")
  let mut is := #[]
  let t := t.raw
  -- Collect all identifiers to introduce them as parameters
  for s in t.topDown do
    if s.isIdent && !is.contains s then
      is := is.push s
  -- Rewrite `∘` to `inst.op` to avoid type class inference
  let t ← t.rewriteBottomUpM fun s => match s with
    | `($a ∘ $b) => `($(inst).op $a $b)
    | _ => pure s
  -- Assemble term and command
  let mut t : Term := ⟨t⟩
  for i in is.reverse do
    t ← `(∀ $(⟨i⟩) : $G, $t)
  elabCommand (← `(command| abbrev%$tk $eqName ($G : Type _) [$inst : Magma $G] := $t))
