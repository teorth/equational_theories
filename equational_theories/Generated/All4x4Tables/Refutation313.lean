
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [221, 2277, 2281, 2314, 2318, 2368, 2372, 3684] [205, 208, 231, 2240, 2340, 2441, 2644, 3458, 3461, 3472, 3475, 3482, 3519, 3522, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3674, 3675, 3677, 3678, 3685, 3687, 3714, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 4065, 4276] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 1, 3], [3, 3, 1, 3], [3, 0, 0, 3], [0, 1, 2, 3]]», by decideFin!⟩
