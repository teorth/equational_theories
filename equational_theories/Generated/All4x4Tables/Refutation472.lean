
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [345, 349, 354, 393, 397, 401, 3354, 3358, 3433, 3444, 3445, 3452, 3547, 3557, 3597, 3614, 3636, 3641, 3750, 3754, 3776, 3781, 3787, 3794, 3804, 3808, 3815, 3852, 3854, 3923, 3937, 3941, 3945, 4020, 4022, 4027, 4047, 4054, 4061, 4160, 4170, 4183, 4197, 4202, 4216, 4223, 4227, 4233, 4238, 4253, 4377, 4535, 4537, 4556, 4563, 4567, 4568, 4681] [2, 3, 8, 23, 47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3], [3, 3, 3, 3]]», by decideFin!⟩
