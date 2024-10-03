import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [437] [413,440,443,444,817,818,819,820,821,823,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,854,858,1023,1036,1039,1042,1043,1046,1049,1052,1053,1056,1060,1064,1068,1224,1226,1227,1229,1230,1239,1240,1242,1243,1245,1246,1247,1249,1250,1252,1253,1255,1256,1257,1259,1260,1261,1263,1264,1265,1267,1271,1835,1851,1855,1861,1865,3256,3315,3318,3321,3323,3660,3661,3663,3665,3721,3724,3726,3727,3729,3862,3865,3870,3873,3925,3928,3931,3935,3943,4066,4067,4068,4069,4070,4071,4072,4073,4076,4269,4270,4314,4316,4318,4341,4583,4584,4597,4598,4601,4631,4673] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]», by decideFin!⟩
