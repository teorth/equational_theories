
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1523, 2132, 2282, 2470] [3050, 3456, 3862, 4598, 4656] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[4,3,1,0,2],[3,2,4,1,0]]», by decideFin!⟩
