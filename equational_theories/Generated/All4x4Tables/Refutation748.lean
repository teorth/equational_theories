
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,0,3,4,5],[2,4,0,4,4,4],[2,1,2,3,4,5],[0,1,2,5,5,5],[0,3,2,3,3,3],[0,4,2,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,0,3,4,5],[2,4,0,4,4,4],[2,1,2,3,4,5],[0,1,2,5,5,5],[0,3,2,3,3,3],[0,4,2,4,4,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,1,0,3,4,5],[2,4,0,4,4,4],[2,1,2,3,4,5],[0,1,2,5,5,5],[0,3,2,3,3,3],[0,4,2,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,0,3,4,5],[2,4,0,4,4,4],[2,1,2,3,4,5],[0,1,2,5,5,5],[0,3,2,3,3,3],[0,4,2,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2683] [323] :=
    ⟨Fin 6, «FinitePoly [[0,1,0,3,4,5],[2,4,0,4,4,4],[2,1,2,3,4,5],[0,1,2,5,5,5],[0,3,2,3,3,3],[0,4,2,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
