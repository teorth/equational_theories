
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 1 * x + 0 * y + 1 * x * y) % 3' (0, 98, 103, 1019, 1037, 1222, 1227, 1237, 1247, 1257, 3252, 3315, 4586, 4665)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + x + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + x + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 2 * y² + x + x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [104, 1038, 3316, 4587] [47, 102, 105, 107, 108, 115, 117, 118, 124, 125, 127, 151, 203, 255, 307, 411, 614, 817, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1039, 1045, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1224, 1225, 1226, 1229, 1231, 1232, 1239, 1241, 1242, 1249, 1251, 1252, 1275, 1276, 1278, 1279, 1285, 1286, 1288, 1289, 1312, 1313, 1315, 1316, 1322, 1323, 1325, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly 2 * x² + 2 * y² + x + x * y % 3», Finite.of_fintype _, by decideFin!⟩
