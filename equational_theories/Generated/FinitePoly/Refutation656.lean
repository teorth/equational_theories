
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 1 * x + 3 * y + 0 * x * y) % 5' (0, 150, 159, 166, 202, 211, 220, 410, 416, 428, 439, 451, 472, 500, 512, 561, 1222, 1251, 1275, 1277, 1284, 4272, 4292, 4331, 4597, 4657, 4672)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly x + 3 * y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => x + 3 * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly x + 3 * y % 5» :
  ∃ (G : Type) (_ : Magma G), Facts G [160, 167, 212, 221, 452, 501, 562, 1252, 1276, 1278, 1285, 4332] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 152, 153, 154, 156, 157, 159, 166, 169, 170, 176, 177, 179, 204, 205, 206, 208, 209, 211, 218, 219, 222, 228, 229, 231, 255, 307, 331, 359, 407, 412, 413, 414, 416, 419, 420, 426, 427, 430, 436, 437, 439, 463, 464, 466, 467, 474, 476, 477, 500, 503, 504, 510, 511, 614, 817, 1020, 1224, 1225, 1226, 1228, 1229, 1231, 1232, 1238, 1239, 1241, 1242, 1248, 1249, 1251, 1275, 1279, 1286, 1288, 1289, 1312, 1313, 1315, 1316, 1322, 1323, 1325, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4065, 4258, 4268, 4269, 4270, 4272, 4275, 4276, 4283, 4284, 4290, 4291, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4683, 4688] :=
    ⟨Fin 5, «FinitePoly x + 3 * y % 5», by decideFin!⟩
