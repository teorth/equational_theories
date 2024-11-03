
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,5,1,1],[3,4,2,0,1,5],[5,1,4,3,2,0],[1,0,2,4,3,5],[3,2,1,5,2,3],[2,1,0,3,5,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,5,1,1],[3,4,2,0,1,5],[5,1,4,3,2,0],[1,0,2,4,3,5],[3,2,1,5,2,3],[2,1,0,3,5,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,3,5,1,1],[3,4,2,0,1,5],[5,1,4,3,2,0],[1,0,2,4,3,5],[3,2,1,5,2,3],[2,1,0,3,5,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,5,1,1],[3,4,2,0,1,5],[5,1,4,3,2,0],[1,0,2,4,3,5],[3,2,1,5,2,3],[2,1,0,3,5,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1685] [1691, 3253, 4321, 4658] :=
    ⟨Fin 6, «FinitePoly [[1,2,3,5,1,1],[3,4,2,0,1,5],[5,1,4,3,2,0],[1,0,2,4,3,5],[3,2,1,5,2,3],[2,1,0,3,5,4]]», Finite.of_fintype _, by decideFin!⟩
