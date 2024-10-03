import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [162,1461,1465,1469,1473,1660,1676,1871,1879,3089] [3058,3061,3075,3081,3085,3093,3097,4073,4076,4121,4124,4142,4146,4150,4599,4602,4655,4675] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,3,2,3],[2,1,2,1],[0,1,0,1]]», by decideFin!⟩
