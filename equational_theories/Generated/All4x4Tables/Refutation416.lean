import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,0],[3,1,1,1],[2,3,2,2],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,0],[3,1,1,1],[2,3,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,0],[3,1,1,1],[2,3,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,0],[3,1,1,1],[2,3,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3321] [3322,3323,4269,4270,4316,4318,4341,4583,4597] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,0],[3,1,1,1],[2,3,2,2],[3,3,3,3]]», by decideFin!⟩
