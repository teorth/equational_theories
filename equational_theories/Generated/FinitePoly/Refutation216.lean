
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 2 * y**2 + 1 * x + 0 * y + 0 * x * y) % 3' (0, 254, 263, 816, 845, 1019, 1048, 3252, 3318, 4597, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * y² + x % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * y*y + x

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * y² + x % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [264, 846, 1049, 3319] [47, 99, 151, 203, 258, 261, 263, 271, 273, 274, 280, 281, 283, 307, 411, 614, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 836, 842, 843, 845, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly 2 * y² + x % 3», Finite.of_fintype _, by decideFin!⟩
