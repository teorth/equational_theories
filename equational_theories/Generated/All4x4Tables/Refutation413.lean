
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [307, 1020, 1240, 1244, 3255, 3661, 3662, 3724] [8, 100, 101, 102, 105, 107, 108, 114, 115, 117, 118, 124, 125, 127, 308, 309, 310, 312, 313, 315, 323, 325, 326, 333, 335, 359, 411, 817, 1021, 1022, 1023, 1025, 1026, 1028, 1029, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1072, 1073, 1075, 1076, 1082, 1083, 1085, 1086, 1109, 1110, 1112, 1113, 1119, 1120, 1122, 1226, 1229, 1231, 1232, 1242, 1249, 1251, 1252, 1275, 1276, 1278, 1279, 1285, 1286, 1288, 1289, 1312, 1313, 1315, 1316, 1322, 1323, 1325, 1832, 3256, 3319, 3665, 3712, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 3], [3, 1, 1, 1], [2, 2, 2, 2], [2, 3, 3, 3]]», by decideFin!⟩
