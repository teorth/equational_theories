
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [414, 3906] [23, 417, 427, 436, 440, 464, 513, 1020, 1629, 1832, 2441, 2644, 3050, 3459, 3481, 3509, 3518, 3522, 3556, 3712, 3748, 3752, 3759, 3864, 3865, 3867, 3868, 3871, 3877, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4073, 4081, 4118, 4127, 4131, 4154, 4165, 4273, 4320, 4585, 4605] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]», by decideFin!⟩
