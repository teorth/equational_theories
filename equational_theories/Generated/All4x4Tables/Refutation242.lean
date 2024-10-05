
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,1],[3,1,2,1],[1,2,2,3],[2,1,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,1],[3,1,2,1],[1,2,2,3],[2,1,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,1],[3,1,2,1],[1,2,2,3],[2,1,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,1],[3,1,2,1],[1,2,2,3],[2,1,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3555, 3722] [3253, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3558, 3712, 3714, 3721, 3724, 3725, 3748, 3749, 3752, 3759, 3761, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3961, 3962, 3964, 4065, 4283, 4284, 4290, 4291, 4314, 4320, 4380, 4599, 4605, 4606, 4608, 4629, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,1],[3,1,2,1],[1,2,2,3],[2,1,3,3]]», by decideFin!⟩
