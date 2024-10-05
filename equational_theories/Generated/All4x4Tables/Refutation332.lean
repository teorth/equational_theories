
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,1,3],[3,0,2,2],[1,1,3,0],[0,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,1,3],[3,0,2,2],[1,1,3,0],[0,2,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,1,3],[3,0,2,2],[1,1,3,0],[0,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,1,3],[3,0,2,2],[1,1,3,0],[0,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2240, 2254, 2264, 2937] [40, 43, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2246, 2256, 2266, 2699, 2734, 2743, 2903, 2909, 2939, 3056, 3068, 4071, 4273, 4343, 4591, 4598] :=
    ⟨Fin 4, «FinitePoly [[2,3,1,3],[3,0,2,2],[1,1,3,0],[0,2,0,1]]», by decideFin!⟩
