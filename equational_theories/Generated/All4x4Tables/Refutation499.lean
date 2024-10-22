
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1489, 1516] [614, 817] :=
    ⟨Fin 7, «FinitePoly [[1,2,3,4,5,0,6],[6,3,0,2,1,5,4],[5,4,2,6,0,3,1],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5]]», Finite.of_fintype _, by decideFin!⟩
