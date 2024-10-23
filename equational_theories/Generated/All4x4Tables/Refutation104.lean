
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[2,0,2],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1],[2,0,2],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,2,1],[2,0,2],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1],[2,0,2],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [211, 280, 1452, 1454, 1459, 1523, 1673, 1718, 1835, 2132, 4497] [151, 411, 614, 817, 1020, 1223, 1427, 1428, 1431, 1434, 1435, 1441, 1445, 1632, 1635, 1654, 1691, 1722, 1838, 1840, 1848, 1921, 1925, 2041, 2043, 2060, 2240, 2243, 2244, 2253, 2256, 2257, 2264, 2266, 2293, 2300, 2340, 2443, 2447, 2449, 2457, 2459, 2469, 2496, 2506, 2530, 2543, 2644, 2847, 3050, 3253, 3456, 3667, 3674, 3712, 3721, 3725, 3749, 3752, 3759, 3862, 4065, 4268, 4269, 4275, 4283, 4284, 4290, 4314, 4320, 4396, 4398, 4433, 4435, 4442, 4473, 4480, 4584, 4585, 4587, 4598, 4599, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,2,1],[2,0,2],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
