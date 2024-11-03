
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2381, 2753] [2243, 3306, 3309, 3316, 3343, 3346, 3353, 3509, 3519, 3546, 3556, 3712, 3749, 3752, 3759, 3925, 3952, 3962, 4128, 4165, 4284, 4291, 4320, 4396, 4406, 4435, 4445, 4480, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,1,3,1],[2,1,2,3],[0,1,2,1],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
