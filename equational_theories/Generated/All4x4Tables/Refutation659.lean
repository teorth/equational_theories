
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,3,0,5,0],[5,1,4,1,1,1],[5,4,2,2,2,2],[3,3,3,3,3,3],[5,4,4,4,4,4],[5,5,5,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,3,0,5,0],[5,1,4,1,1,1],[5,4,2,2,2,2],[3,3,3,3,3,3],[5,4,4,4,4,4],[5,5,5,5,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,3,3,0,5,0],[5,1,4,1,1,1],[5,4,2,2,2,2],[3,3,3,3,3,3],[5,4,4,4,4,4],[5,5,5,5,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,3,0,5,0],[5,1,4,1,1,1],[5,4,2,2,2,2],[3,3,3,3,3,3],[5,4,4,4,4,4],[5,5,5,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1037] [3931, 4673] :=
    ⟨Fin 6, «FinitePoly [[0,3,3,0,5,0],[5,1,4,1,1,1],[5,4,2,2,2,2],[3,3,3,3,3,3],[5,4,4,4,4,4],[5,5,5,5,5,5]]», Finite.of_fintype _, by decideFin!⟩
