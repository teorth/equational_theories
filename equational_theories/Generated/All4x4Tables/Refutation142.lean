import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [109,111,371,849,851,1052,1056,1060,1068,1230,1243,1256,1257,1264,1265] [10,104,106,110,378,413,426,427,429,430,432,433,434,437,439,442,443,832,833,834,836,837,838,839,840,841,854,1035,1038,1041,1043,1045,1048,1051,1053,1055,1059,1063,1067,1231,1234,1238,1239,1240,1244,1245,1246,1247,1258,1259,1260,1261,1266,1267,1270,1271,1834,1847,1850,1851,1853,1855,1860,1863,3255,3306,3316,3318,3321,3322,3724,3726,3727,3865,3887,3895,3925,3931,3935,4073,4076,4081,4087,4101,4109,4113,4131,4269,4314,4316,4318,4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]», by decideFin!⟩
