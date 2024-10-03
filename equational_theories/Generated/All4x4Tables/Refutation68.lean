import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [827,1236] [101,103,377,822,824,828,829,830,831,1025,1026,1027,1028,1030,1031,1032,1033,1034,1225,1227,1229,1230,1231,1233,1234,1235,1237,1454,1455,1456,1631,1633,1654,1658,1662,1850,1873,2044,2054,2060,2061,2062,2264,2267,2270,2446,2452,2457,2470,2485,2653,2660,2663,2666,2672,2850,2856,2860,2873,2875,3053,3056,3058,3066,3068,3075,3079,3083,3091,3094,3458,3460,3518,3526,3668,3721,3723,3871,3927,4073,4120,4135,4143,4146,4383,4399,4403,4472,4585,4598,4656,4673] :=
    ⟨Fin 4, «FinitePoly [[0,0,0,1],[1,1,1,0],[1,2,2,2],[3,0,0,3]]», by decideFin!⟩
