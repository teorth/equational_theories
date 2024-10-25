
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,4,1,2],[2,4,3,2,1],[4,2,1,4,3],[1,0,4,4,3],[0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,4,1,2],[2,4,3,2,1],[4,2,1,4,3],[1,0,4,4,3],[0,1,2,3,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,3,4,1,2],[2,4,3,2,1],[4,2,1,4,3],[1,0,4,4,3],[0,1,2,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,4,1,2],[2,4,3,2,1],[4,2,1,4,3],[1,0,4,4,3],[0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2592] [1629, 3261, 3271, 3868, 3887, 3915, 3962, 4320] :=
    ⟨Fin 5, «FinitePoly [[1,3,4,1,2],[2,4,3,2,1],[4,2,1,4,3],[1,0,4,4,3],[0,1,2,3,4]]», Finite.of_fintype _, by decideFin!⟩
