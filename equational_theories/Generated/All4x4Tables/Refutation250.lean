
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,0,1],[1,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,1],[0,0,1],[1,1,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[0,0,1],[1,1,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,1],[0,0,1],[1,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [387] [3306, 3308, 3343, 3345, 3346, 3352, 3353, 3355, 3511, 3518, 3546, 3548, 3549, 3555, 3556, 3558, 3722, 3724, 3748, 3749, 3752, 3759, 3761, 3917, 3924, 3951, 3952, 3954, 3955, 3961, 3962, 4127, 4131, 4154, 4157, 4158, 4164, 4165, 4291, 4293, 4399, 4406, 4408, 4443, 4445, 4479, 4606, 4636, 4658] :=
    ⟨Fin 3, «All4x4Tables [[0,0,1],[0,0,1],[1,1,2]]», Finite.of_fintype _, by decideFin!⟩
