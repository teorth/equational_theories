
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [880] [614, 826, 1426, 3050, 4608] :=
    ⟨Fin 7, «FinitePoly [[1,2,4,0,6,5,3],[4,3,1,5,2,0,6],[0,6,5,1,3,4,2],[5,0,6,2,4,3,1],[3,4,2,6,0,1,5],[2,1,3,4,5,6,0],[6,5,0,3,1,2,4]]», Finite.of_fintype _, by decideFin!⟩
