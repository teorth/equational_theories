
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1],[0,1,2],[1,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,1],[0,1,2],[1,0,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[0,1,2],[1,0,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,1],[0,1,2],[1,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2347, 2787, 2804] [323, 333, 1025, 1847, 2253, 2263, 2300, 2446, 2466, 2649, 3309, 3316, 3343, 3346, 3509, 3519, 3546, 3556, 3712, 3749, 3752, 3759, 3867, 3925, 3952, 3962, 4128, 4165, 4284, 4291, 4320, 4396, 4406, 4435, 4445, 4480, 4606] :=
    ⟨Fin 3, «All4x4Tables [[0,1,1],[0,1,2],[1,0,2]]», Finite.of_fintype _, by decideFin!⟩
