
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,1,4,4],[3,0,3,3,0,3],[5,5,5,0,5,5],[4,1,1,4,1,1],[0,3,0,5,3,0],[2,4,2,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,1,4,4],[3,0,3,3,0,3],[5,5,5,0,5,5],[4,1,1,4,1,1],[0,3,0,5,3,0],[2,4,2,2,2,2]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,4,1,4,4],[3,0,3,3,0,3],[5,5,5,0,5,5],[4,1,1,4,1,1],[0,3,0,5,3,0],[2,4,2,2,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,1,4,4],[3,0,3,3,0,3],[5,5,5,0,5,5],[4,1,1,4,1,1],[0,3,0,5,3,0],[2,4,2,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2260] [203, 1426, 3050, 3456, 4656] :=
    ⟨Fin 6, «FinitePoly [[1,2,4,1,4,4],[3,0,3,3,0,3],[5,5,5,0,5,5],[4,1,1,4,1,1],[0,3,0,5,3,0],[2,4,2,2,2,2]]», Finite.of_fintype _, by decideFin!⟩
