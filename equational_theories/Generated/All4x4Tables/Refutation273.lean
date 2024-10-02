
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
  ∃ (G : Type) (_ : Magma G), Facts G [10, 427, 439, 838, 839, 840, 1046, 1260, 3318] [3, 13, 23, 47, 102, 151, 203, 255, 307, 375, 412, 414, 416, 614, 818, 822, 825, 826, 842, 1026, 1029, 1036, 1226, 1426, 1629, 2035, 2238, 2441, 2644, 2847, 3050, 3254, 3258, 3456, 3660, 3665, 3721, 3722, 3864, 3918, 3943, 4118, 4121, 4380, 4599] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 1], [2, 2, 1, 1], [2, 2, 2, 2], [2, 3, 3, 2]]», by decideFin!⟩
