
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,2,2],[1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[1,2,2],[1,2,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[1,2,2],[1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[1,2,2],[1,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3735] [3258, 3259, 3261, 3262, 3306, 3308, 3309, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3661, 3662, 3667, 3668, 3712, 3721, 3722, 3865, 3868, 3871, 3917, 3924, 3927, 4066, 4068, 4071, 4074, 4120, 4127, 4130, 4269, 4270, 4283, 4284, 4396, 4399, 4435, 4472, 4583, 4598, 4629, 4656] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[1,2,2],[1,2,2]]», Finite.of_fintype _, by decideFin!⟩
