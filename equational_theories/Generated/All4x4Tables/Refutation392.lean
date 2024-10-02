
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 1, 1], [2, 2, 3, 2], [3, 3, 2, 3], [3, 3, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 1, 1], [2, 2, 3, 2], [3, 3, 2, 3], [3, 3, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 1, 1], [2, 2, 3, 2], [3, 3, 2, 3], [3, 3, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 1, 1], [2, 2, 3, 2], [3, 3, 2, 3], [3, 3, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3319, 3515, 4675] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3457, 3459, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3511, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4585, 4587, 4588, 4590, 4591, 4598, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 1, 1], [2, 2, 3, 2], [3, 3, 2, 3], [3, 3, 2, 3]]», by decideFin!⟩
