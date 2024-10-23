
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [618, 827, 1026] [50, 160, 261, 263, 378, 416, 417, 419, 420, 429, 436, 619, 620, 622, 623, 630, 819, 820, 822, 823, 1021, 1022, 1023, 1025, 1028, 1036, 1038, 1039, 1045, 1224, 1225, 1228, 1229, 1231, 1232, 1239, 1241, 1248, 1428, 1429, 1435, 1444, 1445, 1454, 1630, 1631, 1654, 1658, 1833, 1837, 1838, 1850, 1861, 2036, 2044, 2050, 2053, 2054, 2060, 2061, 2243, 2246, 2264, 2267, 2443, 2446, 2457, 2646, 2660, 2672, 2852, 2856, 2873, 2875, 3056, 3058, 3066, 3068, 3075, 3079, 3255, 3256, 3320, 3457, 3458, 3511, 3518, 3519, 3521, 3660, 3662, 3665, 3668, 3721, 3725, 3864, 3867, 3870, 3871, 3917, 3924, 3927, 3928, 4066, 4067, 4068, 4070, 4071, 4073, 4120, 4121, 4127, 4268, 4270, 4314, 4398, 4399, 4435, 4472, 4473, 4583, 4598, 4599, 4631, 4656] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,0],[3,1,0,1],[2,2,2,2],[3,0,0,3]]», Finite.of_fintype _, by decideFin!⟩
