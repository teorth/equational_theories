
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,3,3],[2,3,3,3],[3,0,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,3,3],[2,3,3,3],[3,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,3,3],[2,3,3,3],[3,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,3,3],[2,3,3,3],[3,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [317, 3295] [3264, 3265, 3274, 3275, 3457, 3459, 3461, 3462, 3465, 3471, 3474, 3475, 3481, 3484, 3660, 3661, 3685, 3687, 3862, 4066, 4067, 4071, 4081, 4091, 4093, 4120, 4127, 4131, 4158, 4167, 4269, 4273, 4283, 4291, 4314, 4320, 4321, 4369, 4380, 4583, 4585, 4588, 4591, 4598, 4599, 4605, 4608, 4635, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,3,3],[2,3,3,3],[3,0,3,3]]», by decideFin!⟩
