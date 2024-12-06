
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,1],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[0,0,1],[0,1,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,1],[0,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[0,0,1],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3473, 3683, 3879, 4484] [378, 3254, 3255, 3279, 3281, 3458, 3469, 3475, 3482, 3491, 3495, 3864, 3867, 3881, 3888, 4070, 4084, 4269, 4273, 4275, 4284, 4291, 4314, 4320, 4321, 4396, 4406, 4433, 4443, 4445, 4472, 4480, 4598, 4599, 4606, 4631, 4636, 4647] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[0,0,1],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
