import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [109,367,368,369,849,851,1060,1225,1243,1245,1250,1251,1254,1255,1257,4066,4069,4092,4095,4096,4097,4099] [101,104,111,837,1035,1038,1041,1042,1048,1051,1052,1055,1056,1059,1063,1067,1068,1228,1230,1234,1238,1240,1244,1246,1247,1258,1259,1260,1261,1262,1263,1265,1266,1270,1834,1847,1850,1853,3306,3316,3322,3726,3727,3925,3935,4070,4072,4076,4084,4105,4131,4269,4314,4316,4318,4584,4598,4601,4631,4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[2,2,1,1],[2,2,2,2],[0,2,3,2]]», by decideFin!⟩
