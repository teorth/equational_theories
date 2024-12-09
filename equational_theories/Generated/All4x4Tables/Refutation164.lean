
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,1,0],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[1,1,0],[1,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,1,0],[1,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[1,1,0],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [621, 3928] [50, 56, 99, 151, 203, 255, 411, 623, 629, 630, 632, 633, 639, 640, 642, 643, 669, 676, 680, 707, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3661, 3664, 3665, 3667, 3668, 3712, 3714, 3721, 3722, 3724, 3865, 3867, 3868, 3871, 3878, 3880, 3887, 3915, 3917, 3927, 3955, 3962, 3964, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4120, 4127, 4130, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4629] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[1,1,0],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
