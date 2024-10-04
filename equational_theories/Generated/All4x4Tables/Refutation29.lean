
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,3,0,3],[1,3,3,3],[1,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,3,0,3],[1,3,3,3],[1,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,3,0,3],[1,3,3,3],[1,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,3,0,3],[1,3,3,3],[1,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3894, 4098, 4284, 4423, 4497] [3253, 3456, 3591, 3617, 3660, 3661, 3685, 3687, 3721, 3725, 3865, 3867, 3881, 3887, 3915, 3928, 4070, 4073, 4084, 4105, 4131, 4269, 4273, 4275, 4276, 4283, 4290, 4291, 4293, 4314, 4320, 4321, 4381, 4396, 4398, 4405, 4433, 4435, 4442, 4445, 4473, 4479, 4480, 4583, 4591, 4598, 4599, 4605, 4606, 4608, 4611, 4612, 4620, 4631, 4635, 4636, 4647, 4656, 4673, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,3,0,3],[1,3,3,3],[1,3,3,3]]», by decideFin!⟩
