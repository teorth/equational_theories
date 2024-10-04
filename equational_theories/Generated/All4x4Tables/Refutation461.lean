
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,1],[3,3,0,1],[3,2,1,1],[3,2,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,1],[3,3,0,1],[3,2,1,1],[3,2,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,1],[3,3,0,1],[3,2,1,1],[3,2,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,1],[3,3,0,1],[3,2,1,1],[3,2,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1958, 2093] [1025, 1035, 1045, 1629, 1681, 1691, 1894, 2097, 3306, 3346, 3353, 3867, 3877, 3887, 4320, 4362] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,1],[3,3,0,1],[3,2,1,1],[3,2,0,0]]», by decideFin!⟩
