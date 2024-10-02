
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 0, 3], [3, 1, 1, 3], [0, 1, 0, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 0, 3], [3, 1, 1, 3], [0, 1, 0, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 0, 3], [3, 1, 1, 3], [0, 1, 0, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 0, 3], [3, 1, 1, 3], [0, 1, 0, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [333, 335, 377, 384, 3308, 3345, 3355, 3548, 3555, 3556, 3924, 3954, 3961, 4154, 4157, 4158, 4291, 4293, 4406, 4436, 4443, 4636, 4658] [3315, 3346, 3509, 3558, 3712, 3714, 3721, 3725, 3748, 3752, 3759, 3761, 3928, 3951, 4120, 4165] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 3], [3, 1, 1, 3], [0, 1, 0, 3], [3, 3, 3, 3]]», by decideFin!⟩
