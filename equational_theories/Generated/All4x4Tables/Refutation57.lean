
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,0],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,0],[2,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,0],[2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,0],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [647, 658, 1023, 1256, 1519, 2051, 2128, 2355, 3489, 4398, 4497] [417, 419, 427, 429, 430, 437, 439, 620, 632, 669, 676, 680, 707, 716, 818, 819, 825, 832, 833, 836, 843, 845, 1022, 1025, 1026, 1035, 1038, 1039, 1045, 1046, 1048, 1113, 1224, 1225, 1228, 1231, 1238, 1239, 1241, 1242, 1249, 1251, 1289, 1479, 1632, 1635, 1654, 1684, 1691, 1834, 1840, 1847, 1848, 1850, 1851, 1860, 1894, 1921, 1934, 2053, 2060, 2088, 2090, 2097, 2137, 2241, 2244, 2256, 2263, 2267, 2291, 2293, 2300, 2338, 2447, 2457, 2470, 2534, 2853, 2863, 2909, 2936, 2940, 2947, 3103, 3112, 3116, 3150, 3255, 3259, 3261, 3269, 3308, 3316, 3318, 3342, 3353, 3462, 3518, 3545, 3549, 3556, 3660, 3661, 3667, 3675, 3724, 3864, 3865, 3868, 3880, 3887, 3925, 3964, 3994, 4071, 4073, 4081, 4083, 4135, 4158, 4167, 4273, 4275, 4283, 4290, 4320, 4383, 4396, 4405, 4435, 4442, 4588, 4598, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,0],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
