import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,0,7,4,5,6],[2,1,0,4,3,7,6,5],[4,0,1,5,2,6,7,3],[0,3,5,6,1,2,4,7],[7,4,2,1,6,5,3,0],[3,7,6,2,5,1,0,4],[5,6,7,3,4,0,1,2],[6,5,4,7,0,3,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,0,7,4,5,6],[2,1,0,4,3,7,6,5],[4,0,1,5,2,6,7,3],[0,3,5,6,1,2,4,7],[7,4,2,1,6,5,3,0],[3,7,6,2,5,1,0,4],[5,6,7,3,4,0,1,2],[6,5,4,7,0,3,2,1]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,2,3,0,7,4,5,6],[2,1,0,4,3,7,6,5],[4,0,1,5,2,6,7,3],[0,3,5,6,1,2,4,7],[7,4,2,1,6,5,3,0],[3,7,6,2,5,1,0,4],[5,6,7,3,4,0,1,2],[6,5,4,7,0,3,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,0,7,4,5,6],[2,1,0,4,3,7,6,5],[4,0,1,5,2,6,7,3],[0,3,5,6,1,2,4,7],[7,4,2,1,6,5,3,0],[3,7,6,2,5,1,0,4],[5,6,7,3,4,0,1,2],[6,5,4,7,0,3,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1885] [3050] :=
    ⟨Fin 8, «FinitePoly [[1,2,3,0,7,4,5,6],[2,1,0,4,3,7,6,5],[4,0,1,5,2,6,7,3],[0,3,5,6,1,2,4,7],[7,4,2,1,6,5,3,0],[3,7,6,2,5,1,0,4],[5,6,7,3,4,0,1,2],[6,5,4,7,0,3,2,1]]», by decideFin!⟩
