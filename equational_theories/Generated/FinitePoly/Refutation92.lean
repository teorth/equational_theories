
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 4 * y**2 + 1 * x + 3 * y + 0 * x * y) % 5' (0, 816, 845, 1019, 1048, 4597, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 4 * y² + x + 3 * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 4 * y*y + x + 3 * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 4 * y² + x + 3 * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [846, 1049, 4673] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 151, 203, 255, 307, 331, 359, 407, 411, 614, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 836, 842, 843, 845, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4065, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 5, «FinitePoly 4 * y² + x + 3 * y % 5», by decideFin!⟩
