import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1029,4091] [8,26,55,56,159,255,264,359,365,411,419,429,436,439,619,642,832,845,1038,1039,1045,1241,1432,1434,1442,1451,1629,1632,1635,1638,1647,1654,1655,1657,1658,1662,1832,1838,1840,1848,1850,1851,1858,1860,1861,1873,2043,2256,2264,2449,2457,2459,2470,2485,3053,3058,3059,3066,3075,3078,3083,3094,3253,3259,3261,3278,3306,3308,3319,3331,3334,3459,3462,3511,3518,3526,3534,3659,3685,3687,3724,3862,3867,3871,3878,3887,3915,3927,4070,4073,4074,4083,4120,4127,4130,4135,4143,4146,4585,4588,4598,4647,4656,4673] :=
    ⟨Fin 4, «FinitePoly [[1,2,0,3],[3,2,1,3],[2,1,3,2],[1,3,2,1]]», by decideFin!⟩
