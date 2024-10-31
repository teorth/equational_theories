
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1],[0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1],[0,0]]» : Magma (Fin 2) where
  op := memoFinOp fun x y => [[1,1],[0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1],[0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [24] [47, 99, 255, 359, 411, 614, 817, 1020, 1223, 1479, 1488, 1515, 1519, 1682, 1684, 1691, 1722, 1731, 1894, 1921, 1925, 2035, 2291, 2293, 2300, 2327, 2340, 2496, 2503, 2530, 2534, 2541, 2543, 2644, 2847, 3105, 3112, 3116, 3143, 3150, 3152, 3271, 3278, 3279, 3342, 3346, 3353, 3472, 3474, 3481, 3545, 3549, 3556, 3558, 3659, 3862, 4083, 4084, 4090, 4091, 4093, 4158, 4165, 4167, 4273, 4275, 4290, 4293, 4320, 4380, 4588, 4590, 4591, 4605, 4606, 4608, 4635, 4636] :=
    ⟨Fin 2, «FinitePoly [[1,1],[0,0]]», Finite.of_fintype _, by decideFin!⟩
