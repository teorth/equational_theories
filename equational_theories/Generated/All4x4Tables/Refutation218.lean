
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2,1],[3,1,0,3],[1,2,2,1],[0,3,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2,1],[3,1,0,3],[1,2,2,1],[0,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,2,1],[3,1,0,3],[1,2,2,1],[0,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2,1],[3,1,0,3],[1,2,2,1],[0,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1682] [414, 473, 477, 513, 617, 622, 667, 676, 680, 716, 825, 872, 906, 1082, 1122, 1285, 1312, 1429, 1434, 1444, 1451, 1479, 1488, 1515, 1519, 1632, 1637, 1645, 1647, 1654, 1691, 1722, 1731, 1838, 1840, 1857, 1861, 1885, 1887, 1921, 1925, 2038, 2041, 2043, 2053, 2060, 2088, 2124, 2128, 2137, 2241, 2244, 2263, 2267, 2447, 2449, 2470, 2647, 2660, 2669, 2699, 2853, 2872, 2900, 2936, 2947, 3056, 3075, 3079, 3103, 3105, 3116, 3139, 3143, 3150, 3261, 3269, 3342, 3346, 3353, 3355, 3459, 3481, 3518, 3545, 3556, 3558, 3662, 3665, 3667, 3675, 3677, 3684, 3714, 3748, 3752, 3761, 3865, 3887, 3924, 3951, 3962, 3964, 4073, 4081, 4120, 4127, 4154, 4167, 4270, 4275, 4283, 4362, 4396, 4398, 4405, 4442, 4473, 4482, 4585, 4590, 4635, 4673] :=
    ⟨Fin 4, «FinitePoly [[0,0,2,1],[3,1,0,3],[1,2,2,1],[0,3,2,1]]», Finite.of_fintype _, by decideFin!⟩
