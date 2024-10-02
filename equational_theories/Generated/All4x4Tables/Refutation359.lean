
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 3, 0, 1], [2, 1, 3, 1], [1, 1, 1, 2], [2, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 3, 0, 1], [2, 1, 3, 1], [1, 1, 1, 2], [2, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 3, 0, 1], [2, 1, 3, 1], [1, 1, 1, 2], [2, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 3, 0, 1], [2, 1, 3, 1], [1, 1, 1, 2], [2, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [107, 1035, 1038, 1051, 3255, 3662] [101, 105, 411, 817, 1041, 1223, 3319, 3660, 3661, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3684, 3685, 3687, 3712, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761] :=
    ⟨Fin 4, «FinitePoly [[1, 3, 0, 1], [2, 1, 3, 1], [1, 1, 1, 2], [2, 3, 3, 3]]», by decideFin!⟩
