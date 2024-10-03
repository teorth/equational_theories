import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1240,1249,1250,1254] [105,106,108,110,378,413,426,427,429,430,432,433,434,437,439,442,443,817,832,833,834,835,837,838,839,840,841,845,846,847,854,1035,1038,1041,1043,1046,1048,1049,1051,1052,1053,1055,1059,1063,1067,1226,1234,1241,1243,1244,1245,1246,1247,1252,1253,1255,1259,1260,1261,1262,1263,1266,1270,1271,1834,1847,1850,1851,1853,1855,1860,1863,3255,3316,3318,3321,3322,3726,3727,3865,3925,3931,3935,4076,4131,4269,4314,4316,4318,4598,4673] :=
    ⟨Fin 4, «FinitePoly [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]», by decideFin!⟩
