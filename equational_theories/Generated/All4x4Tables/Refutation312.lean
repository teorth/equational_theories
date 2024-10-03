import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1445] [151,152,153,156,1427,1428,1429,1430,1435,1442,1444,1446,1448,1629,1631,1634,1637,1638,1640,1647,1654,1657,1660,1668,4131,4283,4358,4398] :=
    ⟨Fin 4, «FinitePoly [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]», by decideFin!⟩
