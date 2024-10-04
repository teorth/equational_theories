
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [823, 2041] [820, 2038, 2043, 2051, 2053, 2060, 2064, 2647, 2660, 2669, 2685, 2688, 2850, 2853, 2891, 3261, 3334, 3459, 3518, 4270, 4283, 4358, 4656, 4673] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]», by decideFin!⟩
