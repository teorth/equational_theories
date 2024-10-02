
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 3, 3], [2, 3, 2, 3], [0, 2, 1, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 3, 3], [2, 3, 2, 3], [0, 2, 1, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 3, 3], [2, 3, 2, 3], [0, 2, 1, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 3, 3], [2, 3, 2, 3], [0, 2, 1, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2256, 2263, 2303, 2327] [24, 25, 26, 28, 29, 31, 203, 307, 1630, 1631, 1632, 1634, 1635, 1637, 1638, 1644, 1645, 1647, 1648, 1654, 1655, 1657, 1658, 1681, 1682, 1684, 1685, 1691, 1692, 1694, 1695, 1718, 1719, 1721, 1722, 1728, 1729, 1731, 2243, 2530, 2644, 3051, 3052, 3053, 3055, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150, 3152, 3253, 3457, 3458, 3459, 3461, 3462, 3464, 3465, 3471, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 3, 3], [2, 3, 2, 3], [0, 2, 1, 3], [0, 1, 2, 3]]», by decideFin!⟩
