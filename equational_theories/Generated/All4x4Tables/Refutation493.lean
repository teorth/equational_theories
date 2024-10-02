
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3364, 4216] [8, 23, 308, 309, 310, 312, 313, 315, 323, 325, 333, 335, 360, 361, 362, 364, 365, 367, 377, 378, 384, 385, 411, 614, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2847, 3050, 3278, 3472, 3662, 3665, 3667, 3675, 3677, 3684, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3878, 4068, 4081, 4273, 4275, 4383, 4386, 4585, 4588] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 3, 1], [3, 2, 2, 0], [3, 2, 2, 0], [1, 0, 0, 3]]», by decideFin!⟩
