
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [343, 378, 3587, 3993, 4533, 4606] [308, 309, 310, 313, 315, 325, 326, 335, 360, 361, 362, 364, 365, 367, 375, 377, 384, 385, 3259, 3261, 3262, 3457, 3459, 3462, 3465, 3519, 3556, 3660, 3661, 3662, 3665, 3667, 3668, 3675, 3677, 3678, 3685, 3687, 3714, 3721, 3724, 3725, 3748, 3751, 3752, 3761, 3925, 3962, 4073, 4081, 4093, 4128, 4155, 4158, 4398, 4406, 4408, 4435, 4472, 4482, 4635] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]», by decideFin!⟩
