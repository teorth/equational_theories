
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,0,3],[0,1,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,0,3],[0,1,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,0,3],[0,1,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,0,3],[0,1,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4544] [4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4358, 4362, 4364, 4369, 4396, 4398, 4433, 4442, 4473, 4480, 4512, 4515, 4598, 4605, 4635, 4673, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,0,3],[0,1,3,3],[3,3,3,3]]», by decideFin!⟩
