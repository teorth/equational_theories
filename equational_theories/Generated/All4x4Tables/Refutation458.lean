
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [104, 109, 368, 427, 1053, 1060, 1257, 1262, 3895, 3902, 4069, 4094, 4609] [10, 14, 16, 101, 102, 105, 114, 115, 117, 118, 124, 125, 127, 378, 412, 413, 416, 417, 419, 420, 426, 429, 430, 437, 439, 463, 464, 466, 467, 473, 474, 476, 477, 500, 501, 503, 504, 510, 511, 513, 822, 825, 826, 832, 833, 836, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1021, 1022, 1026, 1029, 1035, 1038, 1046, 1048, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1229, 1231, 1232, 1239, 1242, 1244, 1275, 1276, 1278, 1279, 1285, 1286, 1288, 1289, 1312, 1313, 1315, 1316, 1322, 1323, 1325, 1834, 1847, 1850, 1851, 1860, 3258, 3262, 3268, 3272, 3863, 4070, 4071, 4073, 4081, 4083, 4084, 4131] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 3], [1, 1, 1, 1], [2, 2, 1, 1], [2, 3, 0, 1]]», by decideFin!⟩
