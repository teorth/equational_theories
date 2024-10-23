
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,6,3,0,2,4],[2,4,3,1,6,5,0],[3,2,0,6,4,1,5],[4,6,2,5,1,0,3],[5,0,1,2,3,4,6],[0,3,5,4,2,6,1],[6,1,4,0,5,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,6,3,0,2,4],[2,4,3,1,6,5,0],[3,2,0,6,4,1,5],[4,6,2,5,1,0,3],[5,0,1,2,3,4,6],[0,3,5,4,2,6,1],[6,1,4,0,5,3,2]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,5,6,3,0,2,4],[2,4,3,1,6,5,0],[3,2,0,6,4,1,5],[4,6,2,5,1,0,3],[5,0,1,2,3,4,6],[0,3,5,4,2,6,1],[6,1,4,0,5,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,6,3,0,2,4],[2,4,3,1,6,5,0],[3,2,0,6,4,1,5],[4,6,2,5,1,0,3],[5,0,1,2,3,4,6],[0,3,5,4,2,6,1],[6,1,4,0,5,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [880] [1223] :=
    ⟨Fin 7, «FinitePoly [[1,5,6,3,0,2,4],[2,4,3,1,6,5,0],[3,2,0,6,4,1,5],[4,6,2,5,1,0,3],[5,0,1,2,3,4,6],[0,3,5,4,2,6,1],[6,1,4,0,5,3,2]]», Finite.of_fintype _, by decideFin!⟩
