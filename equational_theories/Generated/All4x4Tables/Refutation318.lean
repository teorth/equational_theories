import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1056] [99,100,101,105,107,108,109,111,359,360,361,818,821,843,844,847,849,851,1022,1031,1039,1042,1052,1060,1068,1223,1224,1225,1226,1227,1228,1229,1230,1241,1242,1243,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1262,1263,1264,1265,3660,3661,3663,3665,3864,3867,3873,4065,4066,4067,4068,4069,4070,4071,4072,4583,4584,4597,4598,4601,4631] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]», by decideFin!⟩
