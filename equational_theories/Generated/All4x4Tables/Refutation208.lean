import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [100,109,111,819,821,845,848,849,851,1060,1068,1227,1230,1234,1257,1259,1265,1271,3322] [10,104,106,110,359,360,361,378,426,427,429,430,432,433,434,439,442,832,833,834,836,837,838,839,840,841,854,1035,1038,1041,1043,1048,1051,1055,1059,1063,1067,1238,1240,1244,1246,1247,1258,1260,1261,1266,1270,1834,1847,1850,1851,1853,1855,1860,1863,3306,3318,3321,3660,3661,3663,3665,3724,3726,3727,3864,3865,3867,3873,3925,3931,3935,4065,4066,4067,4068,4069,4070,4071,4072,4073,4076,4131,4269,4314,4316,4318,4583,4584,4597,4631] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]», by decideFin!⟩
