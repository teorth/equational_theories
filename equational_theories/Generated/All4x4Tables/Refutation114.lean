import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [427,834,840] [100,105,106,361,819,821,835,837,838,839,841,1023,1036,1039,1042,1043,1046,1049,1052,1053,1056,1060,1064,1068,1224,1226,1227,1229,1230,1239,1240,1242,1243,1245,1246,1247,1249,1250,1252,1253,1255,1256,1257,1259,1260,1261,1263,1264,1265,1267,1271,1835,1851,1855,1857,1860,1861,1863,1865,3256,3306,3315,3318,3321,3323,3661,3663,3725,3726,3727,3729,3865,3873,3928,3931,3943,4066,4067,4068,4069,4070,4071,4072,4073,4076,4270,4314,4318,4341,4583,4584,4597,4598,4601,4631,4673] :=
    ⟨Fin 4, «FinitePoly [[0,2,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,3]]», by decideFin!⟩
