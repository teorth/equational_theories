
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2900] [411, 614, 3050, 4380] :=
    ⟨Fin 7, «FinitePoly [[1,2,5,6,0,3,4],[4,0,1,5,6,2,3],[3,6,4,1,5,0,2],[0,1,2,3,4,5,6],[5,3,6,0,2,4,1],[2,5,3,4,1,6,0],[6,4,0,2,3,1,5]]», Finite.of_fintype _, by decideFin!⟩
