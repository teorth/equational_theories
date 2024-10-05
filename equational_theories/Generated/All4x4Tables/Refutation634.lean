
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,3,3,3],[2,2,2,2,2],[4,4,4,4,4],[2,2,2,2,2],[0,0,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,3,3,3],[2,2,2,2,2],[4,4,4,4,4],[2,2,2,2,2],[0,0,0,0,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,1,3,3,3],[2,2,2,2,2],[4,4,4,4,4],[2,2,2,2,2],[0,0,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,3,3,3],[2,2,2,2,2],[4,4,4,4,4],[2,2,2,2,2],[0,0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3081] [3456] :=
    ⟨Fin 5, «FinitePoly [[1,1,3,3,3],[2,2,2,2,2],[4,4,4,4,4],[2,2,2,2,2],[0,0,0,0,0]]», by decideFin!⟩
