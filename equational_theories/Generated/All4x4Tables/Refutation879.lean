
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,6,5,4,1,0,3],[2,6,3,5,1,0,4],[2,3,5,6,1,0,4],[4,0,1,3,5,6,2],[2,6,5,0,1,3,4],[2,6,5,1,3,0,4],[3,6,5,2,1,0,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,6,5,4,1,0,3],[2,6,3,5,1,0,4],[2,3,5,6,1,0,4],[4,0,1,3,5,6,2],[2,6,5,0,1,3,4],[2,6,5,1,3,0,4],[3,6,5,2,1,0,4]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[2,6,5,4,1,0,3],[2,6,3,5,1,0,4],[2,3,5,6,1,0,4],[4,0,1,3,5,6,2],[2,6,5,0,1,3,4],[2,6,5,1,3,0,4],[3,6,5,2,1,0,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,6,5,4,1,0,3],[2,6,3,5,1,0,4],[2,3,5,6,1,0,4],[4,0,1,3,5,6,2],[2,6,5,0,1,3,4],[2,6,5,1,3,0,4],[3,6,5,2,1,0,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [916] [3887, 3915, 3962, 4275] :=
    ⟨Fin 7, «FinitePoly [[2,6,5,4,1,0,3],[2,6,3,5,1,0,4],[2,3,5,6,1,0,4],[4,0,1,3,5,6,2],[2,6,5,0,1,3,4],[2,6,5,1,3,0,4],[3,6,5,2,1,0,4]]», Finite.of_fintype _, by decideFin!⟩
