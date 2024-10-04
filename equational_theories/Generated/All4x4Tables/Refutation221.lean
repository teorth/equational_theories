
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,1],[1,3,2,0],[3,2,2,2],[0,1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,1],[1,3,2,0],[3,2,2,2],[0,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,1],[1,3,2,0],[3,2,2,2],[0,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,1],[1,3,2,0],[3,2,2,2],[0,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4157] [359, 3253, 3456, 3659, 3862, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4158, 4164, 4165, 4167, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4673, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,1],[1,3,2,0],[3,2,2,2],[0,1,2,0]]», by decideFin!⟩
