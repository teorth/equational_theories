
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2],[0,2,0],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,2],[0,2,0],[1,1,0]]» : Magma (Fin 3) where
  op := finOpTable "[[1,2,2],[0,2,0],[1,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,2],[0,2,0],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1432, 1443, 1630, 1635, 2852, 2909, 3055, 3521, 3880, 3955, 4067, 4083, 4131, 4155, 4268, 4343, 4606, 4658] [151, 203, 255, 359, 1428, 1429, 1431, 1434, 1435, 1444, 1445, 1451, 1454, 1631, 1632, 1634, 1637, 1638, 1644, 1645, 1648, 1654, 1655, 1657, 1832, 2035, 2238, 2443, 2444, 2446, 2447, 2449, 2457, 2459, 2460, 2466, 2467, 2469, 2470, 2644, 2849, 2853, 2855, 2863, 2865, 2872, 2875, 2902, 2936, 2949, 3052, 3056, 3058, 3065, 3066, 3068, 3069, 3075, 3076, 3079, 3105, 3152, 3253, 3457, 3458, 3459, 3461, 3462, 3464, 3465, 3472, 3474, 3481, 3509, 3512, 3518, 3519, 3549, 3556, 3659, 3865, 3867, 3868, 3870, 3871, 3887, 3915, 3917, 3918, 3925, 3928, 3962, 4066, 4068, 4070, 4071, 4073, 4074, 4090, 4120, 4121, 4127, 4128, 4130, 4158, 4165, 4269, 4270, 4272, 4273, 4283, 4284, 4314, 4320, 4321, 4380, 4583, 4584, 4585, 4590, 4598, 4599, 4629, 4635] :=
    ⟨Fin 3, «All4x4Tables [[1,2,2],[0,2,0],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
