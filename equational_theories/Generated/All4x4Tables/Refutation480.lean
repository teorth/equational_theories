
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 1, 3], [2, 3, 1, 0], [3, 0, 1, 2], [1, 3, 0, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 1, 3], [2, 3, 1, 0], [3, 0, 1, 2], [1, 3, 0, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 1, 3], [2, 3, 1, 0], [3, 0, 1, 2], [1, 3, 0, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 1, 3], [2, 3, 1, 0], [3, 0, 1, 2], [1, 3, 0, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [420, 501, 513, 817, 1435, 4276, 4293] [203, 360, 361, 362, 364, 365, 367, 375, 377, 378, 385, 412, 413, 414, 416, 417, 419, 426, 427, 429, 430, 436, 437, 439, 440, 463, 464, 466, 467, 473, 474, 476, 477, 500, 503, 504, 510, 511, 614, 818, 819, 820, 822, 823, 825, 826, 832, 833, 835, 836, 842, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1427, 1428, 1429, 1431, 1432, 1434, 1441, 1442, 1444, 1445, 1451, 1452, 1454, 1455, 1478, 1479, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1528, 1629, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4155, 4157, 4158, 4164, 4165, 4167] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 1, 3], [2, 3, 1, 0], [3, 0, 1, 2], [1, 3, 0, 2]]», by decideFin!⟩
