
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,0,0,0,0],[3,3,3,3,3,3,3],[0,2,2,4,4,0,0],[5,5,5,5,5,5,5],[4,4,2,4,4,4,4],[6,1,6,6,6,6,6],[3,3,3,3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,0,0,0,0],[3,3,3,3,3,3,3],[0,2,2,4,4,0,0],[5,5,5,5,5,5,5],[4,4,2,4,4,4,4],[6,1,6,6,6,6,6],[3,3,3,3,3,3,3]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[0,2,2,0,0,0,0],[3,3,3,3,3,3,3],[0,2,2,4,4,0,0],[5,5,5,5,5,5,5],[4,4,2,4,4,4,4],[6,1,6,6,6,6,6],[3,3,3,3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,0,0,0,0],[3,3,3,3,3,3,3],[0,2,2,4,4,0,0],[5,5,5,5,5,5,5],[4,4,2,4,4,4,4],[6,1,6,6,6,6,6],[3,3,3,3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2890] [2672] :=
    ⟨Fin 7, «FinitePoly [[0,2,2,0,0,0,0],[3,3,3,3,3,3,3],[0,2,2,4,4,0,0],[5,5,5,5,5,5,5],[4,4,2,4,4,4,4],[6,1,6,6,6,6,6],[3,3,3,3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
