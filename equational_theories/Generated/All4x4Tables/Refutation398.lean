import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [156,1442,1444,1446,1837,1838,1847,1858,1867,1868] [153,1435,1448,1629,1631,1634,1637,1638,1640,1647,1654,1657,1660,1668,1840,1850,1860,1869,1871,1875,2035,2050,2051,2053,3253,3258,3259,3261,3262,3306,3308,3309,3459,3462,3465,3862,3917,3924,3927,4073,4121,4284] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]», by decideFin!⟩
