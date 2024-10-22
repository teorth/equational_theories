
import Mathlib.Data.Finite.Basic
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
def «FinitePoly [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3476, 3676, 3879, 4103, 4381, 4389, 4483] [378, 3254, 3255, 3259, 3261, 3269, 3271, 3279, 3281, 3319, 3346, 3353, 3458, 3459, 3481, 3482, 3512, 3522, 3546, 3556, 3666, 3670, 3671, 3680, 3698, 3722, 3752, 3759, 3864, 3867, 3881, 3888, 3915, 3925, 3952, 3962, 4118, 4128, 4155, 4165, 4268, 4269, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4396, 4399, 4406, 4435, 4436, 4442, 4445, 4472, 4473, 4480, 4584, 4585, 4587, 4588, 4598, 4599, 4605, 4606, 4630, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,3,3,3],[1,0,3,3],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
