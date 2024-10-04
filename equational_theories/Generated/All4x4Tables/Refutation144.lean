
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3583, 3587, 3989, 4529, 4533] [3255, 3281, 3309, 3458, 3461, 3481, 3519, 3537, 3556, 3591, 3718, 3725, 3755, 3794, 3864, 3867, 3870, 3880, 3887, 3890, 3925, 3928, 3962, 4067, 4070, 4073, 4080, 4083, 4090, 4093, 4155, 4158, 4165, 4269, 4275, 4284, 4388, 4406, 4435, 4473, 4525, 4606, 4631, 4635, 4666] :=
    ⟨Fin 4, «FinitePoly [[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]», by decideFin!⟩
