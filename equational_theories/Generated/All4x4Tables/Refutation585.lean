
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2381, 2398] [2503, 3306, 3346, 3353, 3546, 3759, 3897, 4128, 4320, 4445] :=
    ⟨Fin 6, «FinitePoly [[0,2,5,5,5,5],[5,1,5,4,5,5],[3,1,2,5,5,5],[0,1,5,3,5,5],[5,1,5,3,4,5],[0,1,2,3,4,5]]», by decideFin!⟩
