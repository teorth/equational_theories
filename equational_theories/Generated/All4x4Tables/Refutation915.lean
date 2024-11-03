
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,5,6,4,3,0],[3,0,6,4,2,5,1],[0,4,3,5,6,1,2],[5,1,4,2,0,6,3],[2,6,1,3,5,0,4],[6,3,2,0,1,4,5],[4,5,0,1,3,2,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,5,6,4,3,0],[3,0,6,4,2,5,1],[0,4,3,5,6,1,2],[5,1,4,2,0,6,3],[2,6,1,3,5,0,4],[6,3,2,0,1,4,5],[4,5,0,1,3,2,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,5,6,4,3,0],[3,0,6,4,2,5,1],[0,4,3,5,6,1,2],[5,1,4,2,0,6,3],[2,6,1,3,5,0,4],[6,3,2,0,1,4,5],[4,5,0,1,3,2,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,5,6,4,3,0],[3,0,6,4,2,5,1],[0,4,3,5,6,1,2],[5,1,4,2,0,6,3],[2,6,1,3,5,0,4],[6,3,2,0,1,4,5],[4,5,0,1,3,2,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [667] [411, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2847, 3050, 3659, 4380] :=
    ⟨Fin 7, «FinitePoly [[1,2,5,6,4,3,0],[3,0,6,4,2,5,1],[0,4,3,5,6,1,2],[5,1,4,2,0,6,3],[2,6,1,3,5,0,4],[6,3,2,0,1,4,5],[4,5,0,1,3,2,6]]», Finite.of_fintype _, by decideFin!⟩
