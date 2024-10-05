
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,2,2,2],[3,2,2,2],[3,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,2,2,2],[3,2,2,2],[3,2,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,2,2,2],[3,2,2,2],[3,2,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,2,2,2],[3,2,2,2],[3,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4535] [4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4396, 4399, 4406, 4433, 4436, 4443, 4470, 4473, 4480, 4583, 4585, 4588, 4591, 4598, 4605, 4608, 4629, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,2,2,2],[3,2,2,2],[3,2,2,2]]», by decideFin!⟩
