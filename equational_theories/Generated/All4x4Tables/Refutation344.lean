import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,2,1],[3,1,2,0],[1,3,2,0],[1,0,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,2,1],[3,1,2,0],[1,3,2,0],[1,0,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,2,1],[3,1,2,0],[1,3,2,0],[1,0,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,2,1],[3,1,2,0],[1,3,2,0],[1,0,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [882,1285] [513,528,575,676,703,1045,1082,1122,1171,1184,1231,1312,1325,1340,1374,1434,1647,1731,1780,1793,1840,1921,1934,1949,1983,2053,2060,2137,2186,2199,2263,2327,2449,2936,3058,3075,3261,3278,3306,3334,3414,3556,3887,4023,4073,4146,4275,4307,4409,4635,4677] :=
    ⟨Fin 4, «FinitePoly [[0,3,2,1],[3,1,2,0],[1,3,2,0],[1,0,2,3]]», by decideFin!⟩
