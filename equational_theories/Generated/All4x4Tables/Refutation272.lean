
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[2,1,1],[1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[2,1,1],[1,2,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[2,1,1],[1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[2,1,1],[1,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [362, 1237, 1457, 2045, 2055, 2463, 2666, 2883, 3669, 3716, 3874, 3930, 4403] [206, 211, 264, 378, 1431, 1432, 1434, 1435, 1441, 1444, 1445, 1634, 1635, 1637, 1638, 1644, 1645, 1648, 1834, 1840, 1841, 1847, 1848, 1857, 1858, 2037, 2038, 2040, 2041, 2050, 2063, 2064, 2241, 2244, 2247, 2253, 2256, 2263, 2266, 2444, 2447, 2450, 2456, 2459, 2466, 2469, 2647, 2649, 2652, 2659, 2662, 2670, 2849, 2853, 2855, 2862, 2866, 2872, 3052, 3055, 3065, 3069, 3076, 3078, 3258, 3259, 3261, 3262, 3306, 3308, 3309, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3661, 3662, 3664, 3665, 3724, 3725, 3867, 3870, 3925, 3928, 4066, 4067, 4070, 4074, 4121, 4128, 4130, 4269, 4270, 4283, 4284, 4398, 4436, 4473, 4583, 4584, 4599, 4629] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[2,1,1],[1,2,2]]», Finite.of_fintype _, by decideFin!⟩
