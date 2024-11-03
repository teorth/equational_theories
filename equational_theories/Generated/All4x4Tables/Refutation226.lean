
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,2],[2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,0,2],[2,2,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,0,2],[2,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,0,2],[2,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3919, 3926, 3929] [3254, 3255, 3256, 3258, 3259, 3261, 3262, 3458, 3459, 3461, 3462, 3464, 3465, 3509, 3664, 3665, 3667, 3668, 3712, 3714, 3864, 3865, 3867, 3868, 3870, 3871, 3915, 4070, 4071, 4073, 4074, 4118, 4120, 4121, 4268, 4269, 4270, 4358, 4396, 4433, 4470, 4584, 4585, 4598, 4599] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,0,2],[2,2,2]]», Finite.of_fintype _, by decideFin!⟩
