
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,6,2,2,6,6,6],[3,2,3,3,2,2,3,2],[3,7,4,1,2,6,0,5],[3,2,0,3,2,6,0,6],[2,2,2,2,2,2,2,2],[2,7,7,7,2,2,2,7],[2,7,5,7,2,6,6,5],[3,7,1,1,2,2,3,7]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,6,2,2,6,6,6],[3,2,3,3,2,2,3,2],[3,7,4,1,2,6,0,5],[3,2,0,3,2,6,0,6],[2,2,2,2,2,2,2,2],[2,7,7,7,2,2,2,7],[2,7,5,7,2,6,6,5],[3,7,1,1,2,2,3,7]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[2,2,6,2,2,6,6,6],[3,2,3,3,2,2,3,2],[3,7,4,1,2,6,0,5],[3,2,0,3,2,6,0,6],[2,2,2,2,2,2,2,2],[2,7,7,7,2,2,2,7],[2,7,5,7,2,6,6,5],[3,7,1,1,2,2,3,7]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,6,2,2,6,6,6],[3,2,3,3,2,2,3,2],[3,7,4,1,2,6,0,5],[3,2,0,3,2,6,0,6],[2,2,2,2,2,2,2,2],[2,7,7,7,2,2,2,7],[2,7,5,7,2,6,6,5],[3,7,1,1,2,2,3,7]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2163] [151, 1428, 1429, 1479, 2050, 2088, 2124, 3457, 3462, 3521, 3877, 3880, 3952, 4314, 4606] :=
    ⟨Fin 8, «FinitePoly [[2,2,6,2,2,6,6,6],[3,2,3,3,2,2,3,2],[3,7,4,1,2,6,0,5],[3,2,0,3,2,6,0,6],[2,2,2,2,2,2,2,2],[2,7,7,7,2,2,2,7],[2,7,5,7,2,6,6,5],[3,7,1,1,2,2,3,7]]», Finite.of_fintype _, by decideFin!⟩
