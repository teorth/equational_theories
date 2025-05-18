import equational_theories.MagmaOp
import equational_theories.Equations.Command

open Lean Elab Law Qq

namespace DualsCommand

theorem flip_dual {Law1 Law2 : NatMagmaLaw} (H : Law1.IsDual Law2.symm) : Law1.IsDual Law2 :=
  fun G _ => (H G).trans
    ⟨satisfies_symm_law, fun h => (MagmaLaw.dual_symm _ ▸ satisfies_symm_law h :)⟩

def checkDual (map : List Nat) : FreeMagma Nat → FreeMagma Nat → Option (List Nat)
  | .Leaf a, .Leaf b =>
    match map[a]? with
    | none => if map.contains b then none else some (map ++ [b])
    | some i => if i = b then some map else none
  | .Fork a1 a2, .Fork b1 b2 => do let map ← checkDual map a1 b1; checkDual map a2 b2
  | _, _ => none

def checkDualLaw : MagmaLaw Nat → MagmaLaw Nat → Option (List Nat × Bool)
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    (do
      let map ← checkDual [] a1 b1
      let map ← checkDual map a2 b2
      return (map, false)) <|>
    (do
      let map ← checkDual [] a1 b2
      let map ← checkDual map a2 b1
      return (map, true))

def getInverse (l : List Nat) : List Nat :=
  (List.range l.length).map fun i => l.idxOf i

elab tk:"duals " i:num " ↔ " j:num : command => Command.liftTermElabM do
  let ns ← getCurrNamespace
  unless ns = EquationsCommand.equationsNamespace do
    throwError "'duals' must be in namespace {EquationsCommand.equationsNamespace}"
  if i.getNat > j.getNat then throwError "reverse this 'duals' command"
  let law1Name := ns.str s!"Law{i.getNat}"
  let law2Name := ns.str s!"Law{j.getNat}"
  let law1 ← unsafe evalConstCheck NatMagmaLaw ``NatMagmaLaw law1Name
  let law2 ← unsafe evalConstCheck NatMagmaLaw ``NatMagmaLaw law2Name
  let thmName := ns.str s!"dual_{i.getNat}"
  let some (map, flip) := checkDualLaw law1 law2.dual | throwError "not duals"
  let ranges := {
    range := (← getDeclarationRange? (← getRef)).getD default
    selectionRange := (← getDeclarationRange? tk).getD default}
  let addMarkup name := do
    Lean.addDeclarationRanges name ranges
    _ ← Term.addTermInfo tk (← mkConstWithLevelParams name) (isBinder := true)

  have law1c : Q(NatMagmaLaw) := mkConst law1Name []
  have law2c : Q(NatMagmaLaw) := mkConst law2Name []
  let go (law2c : Q(NatMagmaLaw)) : MetaM Q(MagmaLaw.IsDual $law1c $law2c) := do
    have mapc : Q(List Nat) := toExpr map
    have invc : Q(List Nat) := toExpr (getInverse map)
    have h1 : Q(($law1c).map (List.getI $mapc) = ($law2c).dual) := (q(Eq.refl ($law2c).dual) : Expr)
    have h2 : Q(($law2c).dual.map (List.getI $invc) = $law1c) := (q(Eq.refl $law1c) : Expr)
    pure q(MagmaLaw.reindex_iff (List.getI $mapc) (List.getI $invc) $h1 $h2)
  let result : Q(IsDual $law1c $law2c) ← if flip then
    pure q(flip_dual $(← go q(($law2c).symm)))
  else
    go q($law2c)
  addAndCompile <| .thmDecl {
    name := thmName
    levelParams := []
    type := q(MagmaLaw.IsDual $law1c $law2c)
    value := result
  }
  addMarkup thmName
  if i.getNat ≠ j.getNat then
    have thm : Q(MagmaLaw.IsDual $law1c $law2c) := mkConst thmName []
    let revName := ns.str s!"dual_{j.getNat}"
    addAndCompile <| .thmDecl {
      name := revName
      levelParams := []
      type := q(MagmaLaw.IsDual $law2c $law1c)
      value := q(($thm).symm)
    }
    addMarkup revName
