
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,4,5,2],[2,0,5,1,3,4],[2,3,5,1,0,4],[1,3,0,4,5,2],[1,0,5,2,3,4],[4,0,3,1,5,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,4,5,2],[2,0,5,1,3,4],[2,3,5,1,0,4],[1,3,0,4,5,2],[1,0,5,2,3,4],[4,0,3,1,5,2]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,3,0,4,5,2],[2,0,5,1,3,4],[2,3,5,1,0,4],[1,3,0,4,5,2],[1,0,5,2,3,4],[4,0,3,1,5,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,4,5,2],[2,0,5,1,3,4],[2,3,5,1,0,4],[1,3,0,4,5,2],[1,0,5,2,3,4],[4,0,3,1,5,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1353] [99, 411, 1248, 1288, 2035, 3862, 4275, 4320, 4606, 4666] :=
    ⟨Fin 6, «FinitePoly [[1,3,0,4,5,2],[2,0,5,1,3,4],[2,3,5,1,0,4],[1,3,0,4,5,2],[1,0,5,2,3,4],[4,0,3,1,5,2]]», Finite.of_fintype _, by decideFin!⟩
