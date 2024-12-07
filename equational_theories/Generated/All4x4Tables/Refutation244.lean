
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,2],[0,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[0,0,2],[0,2,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,2],[0,2,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[0,0,2],[0,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [325, 333, 335, 377, 384, 385, 3318, 3519, 3751] [3315, 3319, 3352, 3521, 3522, 3546, 3558, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3915, 3927, 3951, 3952, 4118, 4164, 4165, 4284, 4290, 4314, 4320, 4396, 4408, 4433, 4445, 4470, 4472, 4473, 4479, 4480, 4598, 4599, 4605, 4606, 4608] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[0,0,2],[0,2,2]]», Finite.of_fintype _, by decideFin!⟩
