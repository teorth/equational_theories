
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,3],[2,1,0,0],[2,1,0,3],[2,0,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,3],[2,1,0,0],[2,1,0,3],[2,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,0,3],[2,1,0,0],[2,1,0,3],[2,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,3],[2,1,0,0],[2,1,0,3],[2,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1904, 4067, 4138] [3309, 3322, 3326, 3334, 3346, 3414, 3890, 3918, 3925, 3928, 3952, 3955, 3962, 4073, 4083, 4093, 4121, 4131, 4158, 4165, 4269, 4272, 4275, 4284, 4314, 4320, 4599, 4606, 4622, 4677] :=
    ⟨Fin 4, «FinitePoly [[2,1,0,3],[2,1,0,0],[2,1,0,3],[2,0,0,3]]», by decideFin!⟩
