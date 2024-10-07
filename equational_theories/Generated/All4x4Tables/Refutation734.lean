
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,5,6,3,1,4],[2,1,3,0,6,4,5],[5,3,2,4,1,6,0],[6,0,4,3,5,2,1],[3,6,1,5,4,0,2],[1,4,6,2,0,5,3],[4,5,0,1,2,3,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,5,6,3,1,4],[2,1,3,0,6,4,5],[5,3,2,4,1,6,0],[6,0,4,3,5,2,1],[3,6,1,5,4,0,2],[1,4,6,2,0,5,3],[4,5,0,1,2,3,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,2,5,6,3,1,4],[2,1,3,0,6,4,5],[5,3,2,4,1,6,0],[6,0,4,3,5,2,1],[3,6,1,5,4,0,2],[1,4,6,2,0,5,3],[4,5,0,1,2,3,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,5,6,3,1,4],[2,1,3,0,6,4,5],[5,3,2,4,1,6,0],[6,0,4,3,5,2,1],[3,6,1,5,4,0,2],[1,4,6,2,0,5,3],[4,5,0,1,2,3,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [704, 1110, 1279, 2328, 2497, 2737, 2903] [513, 826, 833, 1325, 1455, 1731, 1861, 2699, 2743, 2746, 3079, 3152, 4321, 4605, 4636] :=
    ⟨Fin 7, «FinitePoly [[0,2,5,6,3,1,4],[2,1,3,0,6,4,5],[5,3,2,4,1,6,0],[6,0,4,3,5,2,1],[3,6,1,5,4,0,2],[1,4,6,2,0,5,3],[4,5,0,1,2,3,6]]», by decideFin!⟩
