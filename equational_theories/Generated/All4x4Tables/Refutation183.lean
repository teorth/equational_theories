
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 0], [1, 1, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 0], [1, 1, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 0], [1, 1, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 0], [1, 1, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1650, 1724, 1746, 3258, 3268, 3278, 4611, 4622, 4631] [8, 23, 99, 151, 203, 308, 309, 310, 313, 315, 316, 323, 325, 326, 332, 333, 335, 336, 359, 411, 1020, 1223, 1630, 1632, 1634, 1635, 1638, 1645, 1648, 1654, 1655, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1719, 1722, 1728, 1729, 1832, 2035, 2238, 2441, 2644, 3050, 3255, 3316, 3319, 3343, 3353, 3456, 3660, 3661, 3662, 3665, 3667, 3668, 3675, 3677, 3678, 3685, 3687, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3862, 4065, 4291, 4587, 4635] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 0], [1, 1, 2, 2]]», by decideFin!⟩
