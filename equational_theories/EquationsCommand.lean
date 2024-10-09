import Lean
import equational_theories.Magma
import equational_theories.MagmaLaw
import equational_theories.EquationLawConversion

open Lean Elab Command Law

def mkNatMagmaLaw (declName : Name) : ImportM NatMagmaLaw := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck NatMagmaLaw opts ``NatMagmaLaw declName

initialize magmaLawExt : PersistentEnvExtension Name (Name × NatMagmaLaw) (Array (Name × NatMagmaLaw)) ←
  registerPersistentEnvExtension {
    mkInitial := pure .empty
    addImportedFn := Array.concatMapM <| Array.mapM <| fun n ↦ do return (n, ← mkNatMagmaLaw n)
    addEntryFn := Array.push
    exportEntriesFn := .map Prod.fst
  }

def getMagmaLaws {M} [Monad M] [MonadEnv M] : M (Array (Name × NatMagmaLaw)) := do
  return magmaLawExt.getState (← getEnv)

/--
For a more concise syntax, but more importantly to speed up elaboration (where type inference
for each `◇` makes processing this file very slow) we defined custom syntax for defining
equations, and a custom elaborator that instantiates the instante parameter of `◇`.
-/
elab mods:declModifiers tk:"equation " i:num " := " tsyn:term : command => do
  let G := mkIdent (← MonadQuotation.addMacroScope `G)
  let inst := mkIdent (← MonadQuotation.addMacroScope `inst)
  let eqName := .mkSimple s!"Equation{i.getNat}"
  let eqStx := mkNullNode #[tk, i]
  let eqIdent := mkIdentFrom eqStx eqName (canonical := true)
  let finLawName := .mkSimple s!"FinLaw{i.getNat}"
  let finLawIdent := mkIdent finLawName
  let lawName := .mkSimple s!"Law{i.getNat}"
  let lawIdent := mkIdent lawName
  let finThmName := mkIdent (.str finLawName "models_iff")
  let thmName := mkIdent (.str lawName "models_iff")
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
    let docs := s!"```\nequation {i.getNat} := {← PrettyPrinter.formatTerm tsyn}\n```"
    let docs := match declMods.docString? with
      | none => docs
      | some more => s!"{docs}\n\n---\n{more}"
    addDocString' (TSyntax.getId eqIdent) docs
    -- TODO: This will go wrong if we are in a namespace. Is this really needed, or is there
    -- a way to pass the current position already to the `(command|` above?
    Lean.addDeclarationRanges eqName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange eqStx }


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
  let freeMagmaSize := Syntax.mkNumLit (toString is.size)
  -- define law over `Fin n`
  elabCommand (← `(command| abbrev%$tk $finLawIdent : Law.MagmaLaw (Fin $freeMagmaSize) := $tl))
  -- compatibility between the `finLaw` and the original equation
  let modelsIffLemma : Ident := mkIdent (.mkSimple s!"models_iff_{is.size}")
  elabCommand (← `(command| abbrev%$tk $finThmName : ∀ (G : Type _) [$inst : Magma G], G ⊧ $finLawIdent ↔ $eqIdent G := $modelsIffLemma $finLawIdent))
  -- define the actual law over `Nat`
  elabCommand (← `(command| abbrev%$tk $lawIdent : Law.NatMagmaLaw := $tl))
  -- compatibility between the law and the original equation
  elabCommand (← `(command| abbrev%$tk $thmName : ∀ (G : Type _) [$inst : Magma G], G ⊧ $lawIdent ↔ $eqIdent G :=
                    fun G _ ↦ Iff.trans (Law.satisfies_fin_satisfies_nat G $finLawIdent).symm ($finThmName G)))
  -- register the law
  --modifyEnv (magmaLawExt.addEntry · (lawName, ← (mkNatMagmaLaw lawName).run
  --  { env := (← getEnv), opts := (← getOptions) }))
  Command.liftTermElabM do
    -- TODO: This will go wrong if we are in a namespace. Is this really needed, or is there
    -- a way to pass the current position already to the `(command|` above?
    Lean.addDeclarationRanges lawName {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange (← getRef) }
