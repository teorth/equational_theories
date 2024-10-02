
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 0, 1], [1, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 0, 1], [1, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 0, 1], [1, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 0, 1], [1, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [56, 108, 151, 1036, 1038, 1050, 1240, 1243, 1253, 1263] [8, 48, 49, 50, 52, 53, 55, 62, 63, 65, 66, 72, 73, 75, 100, 101, 102, 107, 114, 115, 117, 118, 124, 125, 127, 152, 153, 154, 156, 157, 159, 160, 166, 167, 169, 170, 176, 177, 179, 411, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1039, 1046, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1225, 1226, 1229, 1231, 1232, 1249, 1262, 1275, 1276, 1278, 1279, 1285, 1286, 1288, 1289, 1312, 1313, 1315, 1316, 1322, 1323, 1325, 1832, 3253, 3862, 4276, 4591] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 0, 1], [1, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 0]]», by decideFin!⟩
