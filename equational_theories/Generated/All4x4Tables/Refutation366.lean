
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[3,3,0,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[3,3,0,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[3,3,0,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[3,3,0,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4429, 4430, 4466, 4467, 4487, 4495, 4646] [4396, 4408, 4433, 4445, 4470, 4482, 4583, 4598, 4599, 4605, 4606, 4608, 4622, 4677] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[3,3,0,3],[3,3,3,3]]», by decideFin!⟩
