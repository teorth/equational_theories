
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [117, 1876, 2100, 2939] [3, 8, 23, 39, 411, 513, 1426, 1629, 1835, 1838, 1850, 1857, 1897, 2043, 2124, 2127, 2134, 2238, 2441, 2699, 2743, 2909, 3253, 3456, 4065, 4270, 4598, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,3],[3,1,0,2],[1,3,2,0],[0,2,3,1]]», by decideFin!⟩
