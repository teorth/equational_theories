
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,5,4,3,2],[2,1,3,4,5,0],[3,2,1,0,5,4],[5,3,4,1,2,0],[2,4,0,5,1,3],[4,5,3,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,5,4,3,2],[2,1,3,4,5,0],[3,2,1,0,5,4],[5,3,4,1,2,0],[2,4,0,5,1,3],[4,5,3,2,0,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,0,5,4,3,2],[2,1,3,4,5,0],[3,2,1,0,5,4],[5,3,4,1,2,0],[2,4,0,5,1,3],[4,5,3,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,5,4,3,2],[2,1,3,4,5,0],[3,2,1,0,5,4],[5,3,4,1,2,0],[2,4,0,5,1,3],[4,5,3,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [474] [419, 513, 1629] :=
    ⟨Fin 6, «FinitePoly [[1,0,5,4,3,2],[2,1,3,4,5,0],[3,2,1,0,5,4],[5,3,4,1,2,0],[2,4,0,5,1,3],[4,5,3,2,0,1]]», Finite.of_fintype _, by decideFin!⟩
