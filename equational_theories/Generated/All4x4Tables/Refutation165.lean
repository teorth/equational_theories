import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1082,1109,1887,2706,3481,3677] [411,419,429,436,466,473,500,513,528,562,575,614,622,632,639,669,676,703,716,731,765,778,817,825,835,842,872,879,906,919,934,968,981,1028,1038,1045,1075,1122,1171,1184,1223,1231,1241,1285,1312,1325,1340,1374,1426,1434,1444,1481,1647,1654,1684,1691,1731,1780,1793,1840,1894,1921,1934,1949,1983,2035,2043,2053,2060,2090,2097,2137,2186,2199,2238,2256,2263,2327,2449,2459,2496,2733,2847,2902,2909,2936,3058,3075,3112,3139,3253,3261,3271,3278,3306,3319,3334,3353,3414,3464,3509,3549,3556,3684,3880,3997,4073,4083,4090,4158,4275,4307,4590,4622,4635] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[2,0,1,3],[1,2,0,3],[1,2,0,3]]», by decideFin!⟩
