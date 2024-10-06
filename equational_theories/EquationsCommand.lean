import Lean
import Qq
import equational_theories.EquationLawConversion

open Lean Elab Meta Command

open FreeMagma Law

/--
For a more concise syntax, but more importantly to speed up elaboration (where type inference
for each `◇` makes processing this file very slow) we defined custom syntax for defining
equations, and a custom elaborator that instantiates the instante parameter of `◇`.
-/
elab tk:"equation " i:num " := " t:term : command => do
  let G := mkIdent (← MonadQuotation.addMacroScope `G)
  let inst := mkIdent (← MonadQuotation.addMacroScope `inst)
  let eqName := mkIdent (.mkSimple s!"Equation{i.getNat}")
  let lawName := mkIdent (.mkSimple s!"Law{i.getNat}")
  let thmName := mkIdent (.str lawName.getId "models_iff")
  let mut is := #[]
  let t := t.raw
  -- Collect all identifiers to introduce them as parameters
  for s in t.topDown do
    if s.isIdent && !is.contains s then
      is := is.push s
  let freeEqn ← t.rewriteBottomUpM fun
    | `($lhs = $rhs) => `(MagmaLaw.mk $lhs $rhs)
    | `($a ◇ $b) => `(FreeMagma.Fork $a $b)
    | `($a) =>
      match is.getIdx? a with
      | some i => `(FreeMagma.Leaf $(Syntax.mkNumLit (toString i)))
      | none => `($a)
  let freeEqn : Term := ⟨freeEqn⟩
  let freeMagmaSize := Syntax.mkNumLit (toString is.size)
  let modelsIffLemma : Ident := mkIdent (.mkSimple s!"models_iff_{is.size}")
  -- Rewrite `◇` to `inst.op` to avoid type class inference
  let t ← t.rewriteBottomUpM fun s => match s with
    | `($a ◇ $b) => `($(inst).op $a $b)
    | _ => pure s
  -- Assemble term and command
  let mut t : Term := ⟨t⟩
  for i in is.reverse do
    t ← `(∀ $(⟨i⟩) : $G, $t)
  elabCommand (← `(command| abbrev%$tk $eqName ($G : Type _) [$inst : Magma $G] := $t))
  elabCommand (← `(command| abbrev%$tk $lawName : MagmaLaw (Fin $freeMagmaSize) := $freeEqn))
  elabCommand (← `(command| abbrev%$tk $thmName : ∀ (G : Type _) [$inst : Magma G], G ⊧ $lawName ↔ $eqName G := $modelsIffLemma $lawName))
