
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3505, 3904, 3908, 3911, 4331, 4381, 4461, 4466, 4495] [3459, 3481, 3865, 3887, 4080, 4100, 4108, 4268, 4275, 4283, 4284, 4291, 4362, 4398, 4399, 4436, 4442, 4473, 4479, 4599, 4605, 4610, 4615, 4629, 4635, 4655, 4656, 4658, 4666, 4684] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,3,1,3],[3,3,3,3],[3,3,3,3]]», by decideFin!⟩
