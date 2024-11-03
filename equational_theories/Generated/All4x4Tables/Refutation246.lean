
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,0],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,0],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,0],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,0],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3011] [2238, 2449, 2459, 2503, 2530, 2699, 3075, 3105, 3253, 3459, 3481, 3511, 3518, 3545, 3549, 3556, 3880, 3887, 3915, 3917, 3962, 3964, 4073, 4083, 4127, 4158, 4167, 4273, 4380, 4635, 4656] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,0],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
