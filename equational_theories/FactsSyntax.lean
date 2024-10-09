import Lean
import equational_theories.Magma
import equational_theories.Equations.All

/-!
This defines a compact way of saying “Magma G satisfies this list of equations, but refutes these
others”.
-/

/--
Concise syntax for stating that a given magma satisfies resp. refutes multiple of the equations:

```
Facts G [1, 2] [4, 5] ↔ Equation1 G ∧ Equation2 G ∧ ¬ Equation4 G ∧ ¬ Equation5 G
```
-/
syntax "Facts " term:max " [" num,* "] " " [" num,* "]" : term

-- Many ways to skin the cat here.
-- Using a macro that iterative expands the list was too slow,
-- so here we elaborate to a `Expr` directly.

open Lean Meta Elab Term Tactic Parser.Term in
elab_rules : term | `(Facts $G [ $sats,* ] [ $refs,*]) => do
  let G ← elabTerm G none
  let some u := (← getLevel G).dec | throwError "expected G to be a type"
  let inst ← synthInstance (mkApp (mkConst ``Magma [u]) G)
  let s := sats.getElems.map fun ⟨s⟩ =>
    let n := .mkSimple s!"Equation{s.toNat}"
    mkApp2 (mkConst n [u]) G inst
  let r := refs.getElems.map fun ⟨s⟩ =>
    let n := .mkSimple s!"Equation{s.toNat}"
    mkApp (mkConst ``Not) (mkApp2 (mkConst n [u]) G inst)
  let e := mkAndN (s ++ r).toList
  return e

example (G : Type _) [Magma G] :
   Facts G [1, 2] [4, 5] ↔ Equation1 G ∧ Equation2 G ∧ ¬ Equation4 G ∧ ¬ Equation5 G :=
   Iff.rfl

example (G : Type _) [Magma G] :
   Facts G [1] [4, 5] ↔ Equation1 G ∧ ¬ Equation4 G ∧ ¬ Equation5 G :=
   Iff.rfl

example (G : Type _) [Magma G] :
   Facts G [] [4, 5] ↔ ¬ Equation4 G ∧ ¬ Equation5 G :=
   Iff.rfl

example (G : Type _) [Magma G] :
   Facts G [1, 2] [] ↔ Equation1 G ∧ Equation2 G :=
   Iff.rfl

example (G : Type _) [Magma G] :
   Facts G [] [] ↔ True :=
   Iff.rfl

open Lean Meta Elab Term Tactic Parser.Term in
/--
A relatively crude command for brute-forcing all equations. Given a type and a magma instance and
a tactic, like this:
```
calculate_facts (Fin 2) Magma2a by decide
```
will print out which on equations the tactic succeeds and on which it fails.
-/
elab "calculate_facts " Gs:term:arg insts:term:arg " by " tac:tacticSeq : command => Command.liftTermElabM do
  let G ← elabTerm Gs none
  let some u := (← getLevel G).dec | throwError "expected G to be a type"
  let inst ← elabTerm insts (mkApp (mkConst ``Magma [u]) G)
  let mut s : Array (TSyntax `num) := #[]
  let mut r : Array (TSyntax `num) := #[]
  for n in [1:4694+1] do
    let eqName := .mkSimple s!"Equation{n}"
    let goal ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst eqName [u]) G inst)
    try
      discard <| withCurrHeartbeats <| Tactic.run goal.mvarId! do evalTactic tac
      s := s.push (quote n)
    catch _ =>
      r := r.push (quote n)
  /-
  let factS : Term ← `(term|Facts $Gs [ $(.mk s),* ] [ $(.mk r),* ])
  let suggest ← `(command|
      example : Facts $Gs [ $(.mk (s.map fun n => quote n)),* ] [ $(.mk (r.map fun n => quote n)),* ]
         := by sorry)
  TryThis.addSuggestion tk suggest
  -/
  logInfo m!"These equations can be solved by the tactic:\n{s}\nAnd these cannot:\n{r}"
