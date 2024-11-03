
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[0,1,2],[1,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1],[0,1,2],[1,1,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,1],[0,1,2],[1,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1],[0,1,2],[1,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2499] [55, 65, 75, 107, 124, 127, 159, 231, 263, 273, 283, 413, 416, 419, 426, 429, 436, 439, 466, 473, 476, 503, 513, 622, 629, 632, 639, 642, 669, 676, 679, 706, 713, 716, 819, 825, 835, 842, 845, 872, 879, 882, 906, 1048, 1075, 1082, 1085, 1109, 1112, 1119, 1122, 1231, 1241, 1251, 1278, 1285, 1288, 1312, 1315, 1322, 1428, 1431, 1434, 1444, 1451, 1454, 1488, 1491, 1515, 1518, 1525, 1637, 1657, 1694, 1721, 1728, 1731, 1834, 1840, 1860, 1887, 1897, 1924, 1931, 2037, 2043, 2053, 2060, 2063, 2097, 2100, 2127, 2134, 2137, 2340, 2506, 2533, 2543, 2672, 2709, 2746, 2855, 2865, 2875, 2902, 2912, 2939, 2949, 3058, 3078, 3115, 3142, 3152, 3255, 3256, 3258, 3261, 3268, 3271, 3278, 3281, 3464, 3474, 3481, 3484, 3515, 3549, 3556, 3661, 3667, 3677, 3684, 3687, 3725, 3732, 3752, 3890, 3918, 3925, 3928, 3952, 3955, 3962, 4073, 4083, 4093, 4121, 4131, 4158, 4165, 4269, 4272, 4275, 4399, 4406, 4435, 4442, 4473, 4480, 4590, 4599, 4606, 4677] :=
    ⟨Fin 3, «FinitePoly [[0,1,1],[0,1,2],[1,1,2]]», Finite.of_fintype _, by decideFin!⟩
