import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [58,635,645,649,653,661,819,828,838,845,848,856,860,864] [375,411,413,416,419,422,426,429,432,436,439,442,446,450,454,458,1020,1022,1025,1028,1031,1035,1038,1041,1045,1048,1051,1055,1059,1063,1067,1223,1225,1228,1231,1234,1238,1241,1244,1248,1251,1254,1258,1262,1266,1270,1426,1428,1431,1434,1437,1444,1451,1454,1629,1631,1634,1637,1640,1832,1834,1847,1850,1853,2035,2037,2238,2243,2253,2263,2273,2441,2446,2456,2466,2476,2644,2649,2847,2862,3050,3456,3458,3461,3464,3467,3522,3661,3715,3722,3728,3862,3864,3867,3870,3915,3918,3921,3925,3928,3935,3943,4070,4073,4118,4121,4128,4138,4380,4432,4470,4473,4599] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,1],[3,0,3,1],[3,2,3,1],[3,2,3,1]]», by decideFin!⟩
