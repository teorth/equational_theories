
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 1 * x + 0 * y + 2 * x * y) % 3' (0, 816, 831, 845, 1019, 1034, 1048, 4064, 4130, 4597, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => x + 2 * x * y

/-! The facts -/
theorem «Facts from FinitePoly x + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 832, 846, 1035, 1049, 4131, 4673] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 818, 819, 820, 822, 823, 825, 826, 833, 835, 836, 842, 843, 845, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1036, 1038, 1039, 1045, 1046, 1048, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 3, «FinitePoly x + 2 * x * y % 3», by decideFin!⟩
