
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := finOpTable "[[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3676, 4103] [375, 378, 3666, 3670, 3671, 3680, 3698, 3864, 3867, 3881, 3888, 4128, 4269, 4314, 4320, 4598, 4599, 4605, 4606, 4630, 4631, 4635, 4636, 4647, 4656, 4658, 4666] :=
    ⟨Fin 4, «All4x4Tables [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
