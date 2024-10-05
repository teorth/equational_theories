
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0,6],[5,3,2,0,1,6,4],[6,5,0,2,4,3,1],[0,4,6,5,2,1,3],[4,0,1,3,6,2,5],[2,1,5,6,3,4,0],[3,6,4,1,0,5,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,0,6],[5,3,2,0,1,6,4],[6,5,0,2,4,3,1],[0,4,6,5,2,1,3],[4,0,1,3,6,2,5],[2,1,5,6,3,4,0],[3,6,4,1,0,5,2]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,3,4,5,0,6],[5,3,2,0,1,6,4],[6,5,0,2,4,3,1],[0,4,6,5,2,1,3],[4,0,1,3,6,2,5],[2,1,5,6,3,4,0],[3,6,4,1,0,5,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,0,6],[5,3,2,0,1,6,4],[6,5,0,2,4,3,1],[0,4,6,5,2,1,3],[4,0,1,3,6,2,5],[2,1,5,6,3,4,0],[3,6,4,1,0,5,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2707] [411, 2035, 2743, 2847, 4343] :=
    ⟨Fin 7, «FinitePoly [[1,2,3,4,5,0,6],[5,3,2,0,1,6,4],[6,5,0,2,4,3,1],[0,4,6,5,2,1,3],[4,0,1,3,6,2,5],[2,1,5,6,3,4,0],[3,6,4,1,0,5,2]]», by decideFin!⟩
