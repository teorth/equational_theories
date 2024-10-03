import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,1],[3,3,0,0],[0,0,0,0],[1,1,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,1],[3,3,0,0],[0,0,0,0],[1,1,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,1],[3,3,0,0],[0,0,0,0],[1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,1],[3,3,0,0],[0,0,0,0],[1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1446,1448,1867,1868,1869] [1647,1654,1657,1660,1668,1840,1850,1860,1871,1875,2035,2050,2051,2053,3306,3308,3309,3862,3917,3924,3927,4073,4121,4131,4283,4284,4358,4380,4398,4435,4472,4599] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,1],[3,3,0,0],[0,0,0,0],[1,1,1,1]]», by decideFin!⟩
