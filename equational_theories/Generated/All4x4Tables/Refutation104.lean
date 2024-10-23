
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,1],[2,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,1],[2,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,1],[2,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,1],[2,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4229] [3259, 3261, 3269, 3271, 3414, 3459, 3462, 3474, 3481, 3588, 3737, 3794, 3865, 3868, 3880, 3887, 3994, 4071, 4073, 4081, 4083, 4135, 4273, 4275, 4290, 4320, 4396, 4433, 4473, 4480, 4598, 4605, 4647, 4656] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,1],[2,1,0]]», Finite.of_fintype _, by decideFin!⟩
