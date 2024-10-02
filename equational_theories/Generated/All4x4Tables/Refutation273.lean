
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 0, 1], [2, 2, 1, 1], [2, 2, 2, 2], [2, 3, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 0, 1], [2, 2, 1, 1], [2, 2, 2, 2], [2, 3, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 0, 1], [2, 2, 1, 1], [2, 2, 2, 2], [2, 3, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 0, 1], [2, 2, 1, 1], [2, 2, 2, 2], [2, 3, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [10, 413, 426, 427, 429, 439, 838, 839, 840, 1031, 1041, 1046, 1051, 1055, 1059, 1063, 1241, 1248, 1251, 1260, 1834, 1847, 1850, 3255, 3318, 4269] [3, 23, 47, 151, 203, 255, 307, 375, 412, 414, 416, 614, 818, 822, 842, 1036, 1226, 1426, 1629, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3258, 3456, 3660, 3665, 3715, 3721, 3722, 3864, 3918, 3943, 4118, 4121, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 1], [2, 2, 1, 1], [2, 2, 2, 2], [2, 3, 3, 2]]», by decideFin!⟩
