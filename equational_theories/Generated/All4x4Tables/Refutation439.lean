
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 0, 1], [3, 3, 3, 3], [2, 2, 2, 2], [2, 1, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 0, 1], [3, 3, 3, 3], [2, 2, 2, 2], [2, 1, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 0, 1], [3, 3, 3, 3], [2, 2, 2, 2], [2, 1, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 0, 1], [3, 3, 3, 3], [2, 2, 2, 2], [2, 1, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4066, 4608] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3659, 3862, 4067, 4068, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 0, 1], [3, 3, 3, 3], [2, 2, 2, 2], [2, 1, 2, 2]]», by decideFin!⟩
