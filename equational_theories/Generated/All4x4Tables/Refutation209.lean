import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [837,847,1022,1046,1051,1052,1240,1242,1243,1245,1249,1254,1259,1263] [8,10,11,100,101,106,109,110,111,359,360,361,378,411,413,414,426,427,429,430,432,433,434,436,437,439,440,442,443,444,819,820,821,823,832,833,834,838,839,840,841,842,843,844,848,849,850,851,854,858,1023,1025,1028,1031,1036,1039,1042,1056,1060,1064,1068,1226,1227,1229,1230,1231,1256,1257,1264,1265,1267,1832,1835,1857,1861,1865,3253,3256,3306,3315,3319,3323,3659,3660,3661,3662,3663,3665,3721,3724,3725,3729,3862,3864,3867,3870,3873,3915,3928,3943,4065,4066,4067,4068,4069,4070,4071,4072,4073,4270,4341,4583,4584,4597,4601,4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]», by decideFin!⟩
