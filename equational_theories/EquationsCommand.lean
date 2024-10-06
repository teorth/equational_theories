import Lean
import equational_theories.Magma
import equational_theories.MagmaLaw

open Lean Elab Command

/--
For a more concise syntax, but more importantly to speed up elaboration (where type inference
for each `◇` makes processing this file very slow) we defined custom syntax for defining
equations, and a custom elaborator that instantiates the instante parameter of `◇`.
-/
elab mods:declModifiers tk:"equation " i:num " := " tsyn:term : command => do
  let G := mkIdent (← MonadQuotation.addMacroScope `G)
  let inst := mkIdent (← MonadQuotation.addMacroScope `inst)
  let eqName := mkIdent (.mkSimple s!"Equation{i.getNat}")
  let lawName := mkIdent (.mkSimple s!"Law{i.getNat}")
  let mut is := #[]
  let t := tsyn.raw
  -- Collect all identifiers to introduce them as parameters
  for s in t.topDown do
    if s.isIdent && !is.contains s then
      is := is.push s
  -- Rewrite `◇` to `inst.op` to avoid type class inference
  let t ← t.rewriteBottomUpM fun s => match s with
    | `($a ◇ $b) => `($(inst).op $a $b)
    | _ => pure s
  -- Assemble term and command
  let mut t : Term := ⟨t⟩
  for i in is.reverse do
    t ← `(∀ $(⟨i⟩) : $G, $t)
  elabCommand (← `(command| abbrev%$tk $eqName ($G : Type _) [$inst : Magma $G] := $t))
  -- Create law
  let tl := tsyn.raw
  let tl ← tl.rewriteBottomUpM fun s => match s with
    | `($a ◇ $b) => `(FreeMagma.Fork $a $b)
    | `($a = $b) => `(Law.MagmaLaw.mk $a $b)
    | _ => pure s
  -- replace identifier `i` with `idx`.
  let tl ← tl.rewriteBottomUpM fun s =>
    match is.indexOf? s with
      | some idx => `(FreeMagma.Leaf $(quote idx.val))
      | none => pure s
  let mut tl : Term := ⟨tl⟩
  elabCommand (← `(command| abbrev%$tk $lawName : Law.MagmaLaw Nat := $tl))
  Command.liftTermElabM do
    let declMods ← elabModifiers mods
    -- Create a decl named `declName`
    addDocString' (TSyntax.getId eqName) declMods.docString?
