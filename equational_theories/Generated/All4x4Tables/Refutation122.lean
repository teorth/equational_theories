
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,2],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[0,0,2],[1,1,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,2],[1,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[0,0,2],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [372, 4101] [3253, 3456, 3664, 3667, 3668, 3674, 3675, 3678, 3712, 3714, 3721, 3722, 3724, 3725, 3862, 4071, 4083, 4118, 4120, 4121, 4127, 4130, 4131, 4155, 4165, 4268, 4269, 4272, 4273, 4276, 4284, 4293, 4314, 4320, 4321, 4343, 4380, 4584, 4588, 4598, 4606, 4629, 4635, 4636, 4684] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[0,0,2],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
