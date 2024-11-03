
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,2,1],[0,4,0,0,0],[3,0,3,0,3],[2,0,0,2,2],[1,1,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,2,1],[0,4,0,0,0],[3,0,3,0,3],[2,0,0,2,2],[1,1,1,1,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,3,2,1],[0,4,0,0,0],[3,0,3,0,3],[2,0,0,2,2],[1,1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,2,1],[0,4,0,0,0],[3,0,3,0,3],[2,0,0,2,2],[1,1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1868] [151, 1428, 1429, 1435, 1629, 1840, 1847, 1857, 1860, 2035, 3253, 3459, 3462, 3465, 3862, 4073, 4121, 4131, 4283, 4284, 4314, 4380, 4599] :=
    ⟨Fin 5, «FinitePoly [[1,2,3,2,1],[0,4,0,0,0],[3,0,3,0,3],[2,0,0,2,2],[1,1,1,1,1]]», Finite.of_fintype _, by decideFin!⟩
