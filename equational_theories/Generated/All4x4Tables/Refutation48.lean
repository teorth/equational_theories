
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[2,0,3,3],[1,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[2,0,3,3],[1,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[2,0,3,3],[1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[2,0,3,3],[1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3269, 3283, 3294] [3456, 3660, 3661, 3667, 3675, 3685, 3687, 3712, 3749, 3759, 3864, 3865, 3867, 3868, 3870, 3871, 3877, 3878, 3881, 3887, 3888, 3890, 4066, 4067, 4091, 4093, 4165, 4269, 4273, 4275, 4283, 4284, 4290, 4293, 4300, 4314, 4320, 4321, 4380, 4583, 4591, 4606, 4608, 4631, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[2,0,3,3],[1,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
