import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1931,1975,2134] [151,153,156,166,1426,1428,1444,1481,1629,1631,1634,1637,1640,1647,1654,1657,1660,1668,1684,1691,1694,1697,1705,2127,3862,3867,3880,3887,3890,3901,3952,3962,3972,4065,4073,4093,4606] :=
    ⟨Fin 4, «FinitePoly [[2,1,1,1],[3,1,0,2],[1,1,3,1],[1,1,1,0]]», by decideFin!⟩
