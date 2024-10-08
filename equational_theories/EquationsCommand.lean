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
  let eqName := .mkSimple s!"Equation{i.getNat}"
  let eqIdent := mkIdent eqName
  let lawName := .mkSimple s!"Law{i.getNat}"
  let lawIdent := mkIdent lawName
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
  elabCommand (← `(command| abbrev%$tk $eqIdent ($G : Type _) [$inst : Magma $G] := $t))
  Command.liftTermElabM do
    let declMods ← elabModifiers mods
    addDocString' (TSyntax.getId eqIdent) declMods.docString?
    -- TODO: This will go wrong if we are in a namespace. Is this really needed, or is there
    -- a way to pass the current position already to the `(command|` above?
    Lean.addDeclarationRanges eqName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange (← getRef) }


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
  elabCommand (← `(command| abbrev%$tk $lawIdent : Law.MagmaLaw Nat := $tl))
  Command.liftTermElabM do
    -- TODO: This will go wrong if we are in a namespace. Is this really needed, or is there
    -- a way to pass the current position already to the `(command|` above?
    Lean.addDeclarationRanges lawName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange (← getRef) }
