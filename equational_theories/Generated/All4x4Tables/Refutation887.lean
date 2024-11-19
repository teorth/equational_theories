
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,4,1,3,6,2],[3,0,5,6,2,0,4],[6,4,0,5,0,1,3],[4,0,6,0,5,2,1],[2,6,1,0,2,3,5],[1,2,3,4,6,1,0],[5,3,0,2,1,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,4,1,3,6,2],[3,0,5,6,2,0,4],[6,4,0,5,0,1,3],[4,0,6,0,5,2,1],[2,6,1,0,2,3,5],[1,2,3,4,6,1,0],[5,3,0,2,1,4,5]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,5,4,1,3,6,2],[3,0,5,6,2,0,4],[6,4,0,5,0,1,3],[4,0,6,0,5,2,1],[2,6,1,0,2,3,5],[1,2,3,4,6,1,0],[5,3,0,2,1,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,4,1,3,6,2],[3,0,5,6,2,0,4],[6,4,0,5,0,1,3],[4,0,6,0,5,2,1],[2,6,1,0,2,3,5],[1,2,3,4,6,1,0],[5,3,0,2,1,4,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3961] [3659, 4321] :=
    ⟨Fin 7, «FinitePoly [[1,5,4,1,3,6,2],[3,0,5,6,2,0,4],[6,4,0,5,0,1,3],[4,0,6,0,5,2,1],[2,6,1,0,2,3,5],[1,2,3,4,6,1,0],[5,3,0,2,1,4,5]]», Finite.of_fintype _, by decideFin!⟩
