
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,2,2,3],[2,2,2,3],[3,3,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,2,2,3],[2,2,2,3],[3,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,2,2,3],[2,2,2,3],[3,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,2,2,3],[2,2,2,3],[3,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3587, 3600, 4155] [3255, 3261, 3271, 3281, 3309, 3319, 3346, 3458, 3461, 3464, 3474, 3481, 3484, 3509, 3522, 3546, 3661, 3667, 3677, 3687, 3725, 3752, 3864, 3867, 3870, 3880, 3887, 3890, 3915, 3928, 3952, 4067, 4070, 4073, 4080, 4083, 4090, 4093, 4118, 4121, 4165, 4269, 4275, 4284, 4320, 4321, 4343, 4396, 4445, 4470, 4473, 4480, 4584, 4587, 4590, 4599, 4606, 4658, 4677] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,2,2,3],[2,2,2,3],[3,3,2,3]]», by decideFin!⟩
