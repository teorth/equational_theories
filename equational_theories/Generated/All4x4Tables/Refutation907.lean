
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,5,1,1,1,5,5],[2,0,0,2,2,2,0,0],[3,1,1,3,3,3,1,1],[4,2,2,4,4,4,2,2],[7,3,3,7,7,7,3,3],[0,6,6,0,0,0,6,6],[5,7,7,5,5,5,7,7],[6,4,4,6,6,6,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,5,1,1,1,5,5],[2,0,0,2,2,2,0,0],[3,1,1,3,3,3,1,1],[4,2,2,4,4,4,2,2],[7,3,3,7,7,7,3,3],[0,6,6,0,0,0,6,6],[5,7,7,5,5,5,7,7],[6,4,4,6,6,6,4,4]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,5,5,1,1,1,5,5],[2,0,0,2,2,2,0,0],[3,1,1,3,3,3,1,1],[4,2,2,4,4,4,2,2],[7,3,3,7,7,7,3,3],[0,6,6,0,0,0,6,6],[5,7,7,5,5,5,7,7],[6,4,4,6,6,6,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,5,1,1,1,5,5],[2,0,0,2,2,2,0,0],[3,1,1,3,3,3,1,1],[4,2,2,4,4,4,2,2],[7,3,3,7,7,7,3,3],[0,6,6,0,0,0,6,6],[5,7,7,5,5,5,7,7],[6,4,4,6,6,6,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2485] [3050, 4585] :=
    ⟨Fin 8, «FinitePoly [[1,5,5,1,1,1,5,5],[2,0,0,2,2,2,0,0],[3,1,1,3,3,3,1,1],[4,2,2,4,4,4,2,2],[7,3,3,7,7,7,3,3],[0,6,6,0,0,0,6,6],[5,7,7,5,5,5,7,7],[6,4,4,6,6,6,4,4]]», Finite.of_fintype _, by decideFin!⟩
