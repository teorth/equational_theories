
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,0],[1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[2,2,0],[1,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[2,2,0],[1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[2,2,0],[1,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1641, 3262, 3468, 3524] [159, 203, 307, 1427, 1428, 1429, 1431, 1434, 1441, 1445, 1451, 1454, 1632, 1634, 1637, 1644, 1647, 1648, 1654, 1655, 1657, 1832, 2050, 2053, 2238, 2441, 3050, 3255, 3256, 3258, 3259, 3308, 3309, 3315, 3316, 3318, 3319, 3457, 3459, 3461, 3464, 3509, 3511, 3512, 3519, 3522, 3660, 3661, 3662, 3665, 3667, 3668, 3714, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4380, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[2,2,0],[1,1,1]]», Finite.of_fintype _, by decideFin!⟩
