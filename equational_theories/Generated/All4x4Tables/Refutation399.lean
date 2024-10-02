
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 2, 3], [1, 1, 2, 3], [0, 0, 2, 3], [2, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 2, 3], [1, 1, 2, 3], [0, 0, 2, 3], [2, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 2, 3], [1, 1, 2, 3], [0, 0, 2, 3], [2, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 2, 3], [1, 1, 2, 3], [0, 0, 2, 3], [2, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [385, 3529, 3749, 3989, 4006, 4192, 4209, 4396, 4406, 4606] [8, 99, 151, 326, 364, 411, 1020, 1223, 1629, 1832, 2035, 2644, 3319, 3326, 3353, 3522, 3674, 3715, 3722, 3752, 3759, 3867, 3887, 4385, 4445, 4470, 4480] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 2, 3], [1, 1, 2, 3], [0, 0, 2, 3], [2, 1, 2, 3]]», by decideFin!⟩
