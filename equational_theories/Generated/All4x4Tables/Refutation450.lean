import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [420,501,1435] [151,152,153,156,203,1427,1428,1429,1430,1442,1444,1445,1446,1448,1629,1631,1634,1637,1638,1640,1647,1654,1657,1660,1668,1832,1837,1838,1840,1847,1848,1850,1857,1858,1860,1867,1868,1869,1871,1875,2035,2050,2051,2053,3253,3258,3259,3261,3262,3306,3308,3309,3456,3457,3459,3462,3465,3511,3518,3521,3862,3917,3924,3927,4314,4380] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[2,3,1,0],[3,0,1,2],[1,3,0,2]]», by decideFin!⟩
