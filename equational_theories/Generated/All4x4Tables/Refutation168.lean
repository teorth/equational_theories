
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,1,0],[1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,1],[1,1,0],[1,2,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[1,1,0],[1,2,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,1],[1,1,0],[1,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [829, 1236] [377, 378, 822, 1025, 1028, 1225, 1229, 1231, 1631, 2446, 3315, 3316, 3458, 3518, 3519, 3521, 3714, 3721, 3724, 3725, 3924, 3925, 3927, 3928, 4067, 4120, 4121, 4128, 4130, 4314, 4433, 4435, 4436, 4472, 4473, 4598, 4599, 4629] :=
    ⟨Fin 3, «All4x4Tables [[0,0,1],[1,1,0],[1,2,2]]», Finite.of_fintype _, by decideFin!⟩
