
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,2,2,3],[1,2,2,1],[3,3,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,2,2,3],[1,2,2,1],[3,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,2,2,3],[1,2,2,1],[3,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,2,2,3],[1,2,2,1],[3,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3345, 3548, 3555, 3961] [3306, 3353, 3511, 3518, 3521, 3522, 3545, 3546, 3549, 3556, 3558, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3915, 3917, 3924, 3927, 3928, 3951, 3952, 3955, 3962, 3964, 4118, 4120, 4121, 4127, 4131, 4154, 4158, 4164, 4165, 4167, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4396, 4399, 4406, 4408, 4433, 4436, 4443, 4445, 4470, 4472, 4473, 4479, 4480, 4598, 4599, 4605, 4606, 4608, 4629, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,2,2,3],[1,2,2,1],[3,3,1,3]]», Finite.of_fintype _, by decideFin!⟩
