
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [343, 378, 3326, 3587, 3993, 4330, 4533, 4606] [309, 326, 364, 375, 385, 3261, 3519, 3556, 3661, 3677, 3715, 3752, 3925, 3962, 4128, 4155, 4158, 4406, 4435, 4635] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 2, 3], [3, 2, 2, 3], [2, 2, 2, 3], [3, 2, 2, 3]]», by decideFin!⟩
