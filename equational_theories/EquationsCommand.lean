import Lean
import equational_theories.Magma
import equational_theories.MagmaLaw
import equational_theories.EquationLawConversion

open Lean Elab Command Law Qq

initialize magmaLawExt : TagDeclarationExtension ← mkTagDeclarationExtension

def getMagmaLaws : CoreM (Array (Name × NatMagmaLaw)) := do
  let mut out := #[]
  for ns in (magmaLawExt.toEnvExtension.getState (← getEnv)).importedEntries do
    for n in ns do
      out := out.push (n, ← unsafe evalConstCheck NatMagmaLaw ``NatMagmaLaw n)
  return out

namespace EquationsCommand

partial def parseFreeMagma : Term → StateT (Array Ident) Option (FreeMagma Nat)
  | `(($a)) => parseFreeMagma a
  | `($a ◇ $b) => return (← parseFreeMagma a) ◇ (← parseFreeMagma b)
  | x => do
    unless x.raw.isIdent do failure
    let x : Ident := ⟨x.raw⟩
    let ids ← get
    if let some i := ids.findIdx? (· == x) then
      pure (Lf i)
    else
      let i := ids.size
      modify (·.push x)
      pure (Lf i)

def parseMagmaLaw : Term → StateT (Array Ident) Option NatMagmaLaw
  | `($a = $b) => return { lhs := ← parseFreeMagma a, rhs := ← parseFreeMagma b }
  | _ => failure

def magmaToExpr {u : Level} {G : Q(Type u)} (inst : Q(Magma $G)) (xs : Array Q($G)) :
    FreeMagma Nat → Q($G)
  | a ⋆ b => q($(magmaToExpr inst xs a) ◇ $(magmaToExpr inst xs b))
  | Lf i => xs[i]!

def lawToExpr {u : Level} {G : Q(Type u)} (inst : Q(Magma $G)) (xs : Array Q($G)) :
    MagmaLaw Nat → Q(Prop)
  | ⟨a, b⟩ => q($(magmaToExpr inst xs a) = $(magmaToExpr inst xs b))

section -- FIXME: "deriving instance ToExpr for FreeMagma" fails, this is the edited result
universe u

private def toExprFreeMagma {α} [Lean.ToExpr α] [ToLevel.{u}] : FreeMagma.{u} α → Expr
  | .Leaf a =>
    Expr.app (Expr.app (Expr.const `FreeMagma.Leaf [toLevel.{u}]) (toTypeExpr α)) (toExpr a)
  | .Fork a1 a2 =>
    Expr.app (Expr.app (Expr.app (Expr.const `FreeMagma.Fork [toLevel.{u}]) (toTypeExpr α))
      (toExprFreeMagma a1)) (toExprFreeMagma a2)

private instance {α} [Lean.ToExpr α] [ToLevel.{u}] : ToExpr (@FreeMagma.{u} α) where
  toExpr := toExprFreeMagma.{u}
  toTypeExpr := Expr.app (Expr.const `FreeMagma [toLevel.{u}]) (toTypeExpr α)

private def toExprMagmaLaw {α} [Lean.ToExpr α] [ToLevel.{u}] : Law.MagmaLaw.{u} α → Expr
  | ⟨a, a1⟩ =>
    Expr.app (Expr.app (Expr.app (Expr.const `Law.MagmaLaw.mk [toLevel.{u}])
      (toTypeExpr α)) (toExpr a)) (toExpr a1)

instance {α} [Lean.ToExpr α] [ToLevel.{u}] : ToExpr (@Law.MagmaLaw.{u} α) where
  toExpr := toExprMagmaLaw.{u}
  toTypeExpr := Expr.app (Expr.const `Law.MagmaLaw [toLevel.{u}]) (toTypeExpr α)

end

/--
For a more concise syntax, but more importantly to speed up elaboration (where type inference
for each `◇` makes processing this file very slow) we defined custom syntax for defining
equations, and a custom elaborator that instantiates the instante parameter of `◇`.
-/
elab mods:declModifiers tk:"equation " i:num " := " tsyn:term : command => Command.liftTermElabM do
  -- TODO: This will go wrong if we are in a namespace.
  let eqName := .mkSimple s!"Equation{i.getNat}"
  let eqStx := mkNullNode #[tk, i]
  let lawName := .mkSimple s!"Law{i.getNat}"
  let thmName := .str lawName "models_iff"
  let some (law, is) := (parseMagmaLaw tsyn).run #[] | throwError "invalid magma law"
  let declMods ← elabModifiers mods
  let docs := s!"```\nequation {i.getNat} := {← PrettyPrinter.formatTerm tsyn}\n```"
  let docs := match declMods.docString? with
    | none => docs
    | some more => s!"{docs}\n\n---\n{more}"
  let ranges := {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange eqStx }
  let addMarkup name := do
    addDocString' name docs
    Lean.addDeclarationRanges name ranges
    _ ← Term.addTermInfo eqStx (← mkConstWithLevelParams name) (isBinder := true)

  -- define equation
  let u : Level := .param `u
  let value ← withLocalDeclDQ `G q(Type u) fun G : Q(Type u) => do
    withLocalDeclQ `inst .instImplicit q(Magma $G) fun inst =>
    Meta.withLocalDeclsD (is.map fun i => (i.getId, fun _ => pure G)) fun xs => do
    let e ← Meta.mkForallFVars xs (lawToExpr (G := G) inst xs law)
    Meta.mkLambdaFVars #[G, inst] e
  addDecl <| .defnDecl {
    name := eqName
    levelParams := [`u]
    type := q(∀ (G : Type u) [Magma G], Prop)
    value := value
    hints := .abbrev
    safety := .safe
  }
  addMarkup eqName
  have eqConst : Q(∀ (G : Type u) [Magma G], Prop) := .const eqName [u]

  -- define law over `Nat`
  addDecl <| .defnDecl {
    name := lawName
    levelParams := []
    type := q(Law.NatMagmaLaw)
    value := toExpr law
    hints := .opaque
    safety := .safe
  }
  addMarkup lawName
  have lawConst : Q(Law.NatMagmaLaw) := .const lawName []

  -- compatibility between the law and the original equation
  have n : ℕ := is.size
  have : Q(MagmaLaw.bounded $n $lawConst = true) := (q(Eq.refl true) : Expr)
  addDecl <| .thmDecl {
    name := thmName
    levelParams := [`u]
    type := q(∀ (G : Type u) [Magma G], G ⊧ $lawConst ↔ $eqConst G)
    value := q(models_iff_n.{u} $lawConst $n $this)
  }
  addMarkup thmName

  -- register the law
  modifyEnv (magmaLawExt.tag · lawName)
