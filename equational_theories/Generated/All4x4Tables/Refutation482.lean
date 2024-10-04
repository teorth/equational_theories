
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [861, 1793] [23, 411, 614, 820, 823, 835, 842, 1020, 1223, 1832, 3253, 3659, 3862, 4270, 4598] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,4,3],[1,0,3,2,4],[2,4,0,3,1],[3,2,4,1,0],[4,3,1,0,2]]», by decideFin!⟩
