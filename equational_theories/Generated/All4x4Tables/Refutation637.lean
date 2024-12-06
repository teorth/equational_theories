
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3961] [3253, 3509, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3558, 3712, 3714, 3721, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3915, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3962, 3964, 4065, 4283, 4284, 4290, 4291, 4314, 4320, 4343, 4380, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «All4x4Tables [[3,2,3,1],[3,1,1,3],[1,1,2,2],[2,3,2,3]]», Finite.of_fintype _, by decideFin!⟩
