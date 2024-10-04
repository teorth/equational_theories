import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1687] [104,156,364,375,1038,1225,1238,1248,1258,1634,1644,1647,1650,1654,1664,1691,1701,1837,1847,1857,1867,1884,1921,3306,3309,3343,3346,3353,3880,4067,4080,4090,4100,4118,4128,4138,4155,4192,4284,4291,4320,4587,4635,4642,4666] :=
    ⟨Fin 4, «FinitePoly [[2,1,0,1],[2,3,1,1],[2,3,0,2],[0,3,0,1]]», by decideFin!⟩
