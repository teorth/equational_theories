
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[1,1,1,1],[2,0,2,2],[0,3,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[1,1,1,1],[2,0,2,2],[0,3,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[1,1,1,1],[2,0,2,2],[0,3,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[1,1,1,1],[2,0,2,2],[0,3,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [161, 327, 2463] [206, 211, 359, 1431, 1432, 1434, 1435, 1441, 1444, 1445, 1634, 1635, 1637, 1638, 1644, 1645, 1648, 1834, 1840, 1841, 1847, 1848, 1857, 1858, 2241, 2244, 2247, 2253, 2256, 2263, 2266, 2444, 2447, 2450, 2456, 2459, 2466, 2469, 3052, 3055, 3056, 3065, 3068, 3069, 3076, 3078, 3258, 3259, 3261, 3262, 3268, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3342, 3343, 3345, 3346, 3352, 3353, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4066, 4067, 4070, 4071, 4074, 4120, 4121, 4128, 4130, 4269, 4270, 4283, 4284, 4583, 4584, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[1,1,1,1],[2,0,2,2],[0,3,0,0]]», by decideFin!⟩
