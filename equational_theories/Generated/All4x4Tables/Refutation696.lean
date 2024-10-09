
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4541] [4283, 4284, 4290, 4291, 4293, 4396, 4398, 4442, 4473, 4605, 4635] :=
    ⟨Fin 6, «FinitePoly [[3,2,3,5,5,5],[4,3,5,5,5,5],[5,5,5,5,5,5],[5,5,5,5,5,5],[3,5,5,5,5,5],[5,5,5,5,5,5]]», by decideFin!⟩
