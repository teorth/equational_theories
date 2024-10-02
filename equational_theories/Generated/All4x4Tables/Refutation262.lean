
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 3, 1], [3, 2, 3, 0], [1, 0, 2, 3], [1, 0, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 3, 1], [3, 2, 3, 0], [1, 0, 2, 3], [1, 0, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 3, 1], [3, 2, 3, 0], [1, 0, 2, 3], [1, 0, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 3, 1], [3, 2, 3, 0], [1, 0, 2, 3], [1, 0, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1691, 4590] [3, 8, 23, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1630, 1631, 1632, 1634, 1635, 1638, 1644, 1645, 1647, 1648, 1654, 1655, 1657, 1658, 1681, 1682, 1684, 1685, 1692, 1694, 1695, 1719, 1721, 1722, 1728, 1729, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3862, 4065, 4380, 4606] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 3, 1], [3, 2, 3, 0], [1, 0, 2, 3], [1, 0, 2, 3]]», by decideFin!⟩
