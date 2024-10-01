
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 0, 3], [1, 0, 1, 1], [0, 1, 0, 3], [3, 1, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 0, 3], [1, 0, 1, 1], [0, 1, 0, 3], [3, 1, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 0, 3], [1, 0, 1, 1], [0, 1, 0, 3], [3, 1, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 0, 3], [1, 0, 1, 1], [0, 1, 0, 3], [3, 1, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3323, 3350, 3537, 3573, 3943, 3979, 4226, 4229, 4270, 4497, 4622] [8, 40, 411, 817, 1020, 1832, 3258, 3268, 3278, 3457, 3458, 3459, 3461, 3462, 3465, 3471, 3472, 3474, 3475, 3481, 3482, 3484, 3512, 3519, 3521, 3546, 3548, 3555, 3659, 3863, 3864, 3865, 3867, 3868, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3918, 3925, 3927, 3952, 3954, 3961, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4091, 4093, 4121, 4128, 4130, 4155, 4157, 4164, 4381, 4382, 4383, 4385, 4386, 4396, 4399, 4406, 4408, 4433, 4436, 4443, 4445, 4470, 4472, 4473, 4479, 4480] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 0, 3], [1, 0, 1, 1], [0, 1, 0, 3], [3, 1, 3, 2]]», by decideFin!⟩
