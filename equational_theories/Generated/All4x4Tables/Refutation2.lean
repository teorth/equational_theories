
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0],[1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0],[1,0]]» : Magma (Fin 2) where
  op := memoFinOp fun x y => [[0,0],[1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0],[1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [10, 11, 106, 109, 111, 371, 378, 433, 434, 442, 443, 854, 1043, 1053, 1247, 1257, 1265, 1271, 1855, 1863, 3285, 3306, 3321, 3726, 3727, 3895, 3931, 4113, 4293, 4318, 4673] [47, 102, 151, 203, 255, 307, 412, 416, 417, 419, 420, 614, 822, 825, 826, 1021, 1026, 1029, 1232, 1426, 1629, 1833, 1837, 1838, 1840, 1841, 1848, 1858, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3281, 3308, 3309, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3664, 3667, 3668, 3674, 3675, 3678, 3712, 3714, 3722, 3748, 3749, 3751, 3752, 3759, 3761, 3863, 3868, 3871, 3877, 3880, 3890, 3917, 3918, 3924, 3927, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4074, 4080, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4320, 4321, 4343, 4380, 4585, 4587, 4599, 4605, 4629, 4635, 4658] :=
    ⟨Fin 2, «FinitePoly [[0,0],[1,0]]», by decideFin!⟩
