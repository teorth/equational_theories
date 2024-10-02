
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 3], [3, 3, 0, 3], [3, 0, 3, 3], [3, 0, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 3], [3, 3, 0, 3], [3, 0, 3, 3], [3, 0, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 3], [3, 3, 0, 3], [3, 0, 3, 3], [3, 0, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 3], [3, 3, 0, 3], [3, 0, 3, 3], [3, 0, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [321, 3473, 3476, 3479, 3483, 3486, 3489, 3493, 3497, 3501, 4309, 4310] [2, 3, 8, 23, 38, 39, 43, 47, 99, 151, 203, 255, 323, 325, 326, 331, 332, 333, 335, 336, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3337, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3543, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3712, 3714, 3715, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3758, 3759, 3761, 3862, 4055, 4065, 4258, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 3], [3, 3, 0, 3], [3, 0, 3, 3], [3, 0, 0, 3]]», by decideFin!⟩
