
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[0,2,2],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[0,2,2],[2,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[0,2,2],[2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[0,2,2],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3417] [3259, 3261, 3319, 3342, 3459, 3462, 3522, 3545, 3880, 3887, 3915, 3964, 4073, 4083, 4118, 4167, 4273, 4275, 4647, 4656] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[0,2,2],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
