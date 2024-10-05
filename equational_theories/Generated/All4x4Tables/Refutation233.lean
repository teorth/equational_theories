
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3277] [359, 3306, 3456, 3660, 3661, 3667, 3675, 3685, 3687, 3786, 3862, 4070, 4084, 4128, 4155, 4268, 4269, 4273, 4275, 4283, 4284, 4290, 4293, 4300, 4314, 4320, 4321, 4599, 4605, 4606, 4608, 4631, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]», by decideFin!⟩
