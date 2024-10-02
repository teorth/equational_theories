
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 3, 1], [3, 3, 1, 3], [0, 0, 3, 0], [3, 3, 1, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 3, 1], [3, 3, 1, 3], [0, 0, 3, 0], [3, 3, 1, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 3, 1], [3, 3, 1, 3], [0, 0, 3, 0], [3, 3, 1, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 3, 1], [3, 3, 1, 3], [0, 0, 3, 0], [3, 3, 1, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3693, 3910] [307, 359, 3253, 3456, 3664, 3667, 3668, 3674, 3675, 3678, 3863, 3865, 3868, 3871, 3877, 3880, 3887, 3890, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4065, 4269, 4272, 4273, 4276, 4314, 4320, 4321, 4343, 4380, 4583, 4591, 4608, 4635] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 3, 1], [3, 3, 1, 3], [0, 0, 3, 0], [3, 3, 1, 3]]», by decideFin!⟩
