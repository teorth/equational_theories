
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[1,1,1,1],[2,2,3,1],[0,3,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[1,1,1,1],[2,2,3,1],[0,3,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[1,1,1,1],[2,2,3,1],[0,3,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[1,1,1,1],[2,2,3,1],[0,3,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [836] [99, 835, 846, 1223] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[1,1,1,1],[2,2,3,1],[0,3,3,0]]», by decideFin!⟩
