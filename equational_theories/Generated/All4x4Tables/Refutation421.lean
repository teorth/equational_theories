
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,2,3],[2,1,2,3],[2,1,2,3],[1,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[2,1,2,3],[2,1,2,3],[2,1,2,3],[1,1,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[2,1,2,3],[2,1,2,3],[2,1,2,3],[1,1,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[2,1,2,3],[2,1,2,3],[2,1,2,3],[1,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3634] [3255, 3261, 3271, 3281, 3309, 3319, 3346, 3458, 3464, 3474, 3484, 3512, 3522, 3549, 3661, 3667, 3677, 3687, 3725, 3752, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4067, 4073, 4083, 4093, 4121, 4131, 4158, 4269, 4275, 4284, 4320, 4399, 4442, 4470, 4480, 4599, 4622, 4631, 4635] :=
    ⟨Fin 4, «All4x4Tables [[2,1,2,3],[2,1,2,3],[2,1,2,3],[1,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
