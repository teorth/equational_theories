
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,1],[1,1,1,1],[1,3,1,1],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,1],[1,1,1,1],[1,3,1,1],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,1],[1,1,1,1],[1,3,1,1],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,1],[1,1,1,1],[1,3,1,1],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [379] [3253, 3456, 3664, 3665, 3667, 3668, 3712, 3862, 4070, 4071, 4073, 4118, 4120, 4121, 4268, 4269, 4270, 4284, 4314, 4380, 4598, 4599, 4608, 4631, 4656] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,1],[1,1,1,1],[1,3,1,1],[3,3,3,3]]», by decideFin!⟩
