import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2910,2939] [99,117,2035,2100,2125,2644] :=
    ⟨Fin 7, «FinitePoly [[1,2,0,3,6,4,5],[4,1,6,2,5,0,3],[3,5,1,6,4,2,0],[0,4,5,1,3,6,2],[5,6,2,0,1,3,4],[2,3,4,5,0,1,6],[6,0,3,4,2,5,1]]», by decideFin!⟩
