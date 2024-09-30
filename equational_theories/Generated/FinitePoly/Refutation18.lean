
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 1 * y**2 + 2 * x + 0 * y + 3 * x * y) % 4' (0, 39, 306, 309, 311, 315, 319, 322, 3252, 3255, 3257, 3261, 3265, 3267, 3271, 3275, 3277, 3281, 3285, 3287, 3292, 3297, 3302, 3305, 3658, 3661, 3663, 3664, 3667, 3671, 3673, 3676, 3677, 3681, 3683, 3687, 3691, 3693, 3698, 3699, 3703, 3708, 4269, 4271, 4275, 4279, 4340, 4342, 4345, 4350, 4354, 4589, 4621)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + y² + 2 * x + 3 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 2 * x*x + y*y + 2 * x + 3 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + y² + 2 * x + 3 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 320, 323, 3303, 3662, 3668, 3678, 3700, 4346, 4622] [2, 3, 8, 23, 38, 39, 43, 47, 99, 151, 203, 255, 308, 309, 313, 315, 325, 326, 331, 332, 333, 335, 336, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3259, 3261, 3269, 3271, 3279, 3281, 3308, 3309, 3315, 3316, 3318, 3319, 3337, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3543, 3660, 3661, 3667, 3675, 3685, 3687, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3862, 4055, 4065, 4258, 4268, 4269, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly 2 * x² + y² + 2 * x + 3 * x * y % 4», by decideFin!⟩
