
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[3,3,3,3],[1,1,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[3,3,3,3],[1,1,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[3,3,3,3],[1,1,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[3,3,3,3],[1,1,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [366, 3480, 4481] [3254, 3255, 3259, 3261, 3269, 3271, 3279, 3281, 4268, 4273, 4283, 4284, 4290, 4291, 4293, 4307, 4314, 4316, 4320, 4321, 4396, 4398, 4399, 4405, 4406, 4408, 4433, 4435, 4436, 4442, 4443, 4445] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[3,3,3,3],[1,1,3,3],[3,3,3,3]]», by decideFin!⟩
