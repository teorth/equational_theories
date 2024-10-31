
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,0,1],[1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[0,0,1],[1,0,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[0,0,1],[1,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[0,0,1],[1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3478, 3683, 4485] [307, 3255, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3279, 3281, 3306, 3309, 3316, 3459, 3474, 3481, 3484, 3509, 3512, 3519, 3522, 3712, 3722, 3725, 3749, 3759, 3862, 4065, 4268, 4269, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4343, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4442, 4445, 4470, 4473, 4480, 4583, 4585, 4588, 4591, 4598, 4605, 4608, 4629, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[0,0,1],[1,0,0]]», Finite.of_fintype _, by decideFin!⟩
