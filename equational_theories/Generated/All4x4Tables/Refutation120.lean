
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [290, 2347, 2804] [333, 632, 642, 669, 679, 703, 713, 825, 845, 872, 879, 909, 916, 1025, 1434, 1444, 1451, 1491, 1518, 1525, 1647, 1847, 2253, 2263, 2300, 2446, 2466, 2503, 2649, 2787, 3068, 3346, 3474, 3484, 3546, 3556, 3667, 3687, 3752, 3759, 3867, 4128, 4165, 4320, 4399, 4409, 4435, 4445, 4480] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]», by decideFin!⟩
