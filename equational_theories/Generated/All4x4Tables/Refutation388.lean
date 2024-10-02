
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 1, 3], [1, 1, 0, 1], [2, 3, 2, 2], [0, 0, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 1, 3], [1, 1, 0, 1], [2, 3, 2, 2], [0, 0, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 1, 3], [1, 1, 0, 1], [2, 3, 2, 2], [0, 0, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 1, 3], [1, 1, 0, 1], [2, 3, 2, 2], [0, 0, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1022, 1837, 2452, 2646, 2852, 3864] [9, 48, 49, 50, 100, 101, 102, 152, 308, 412, 413, 414, 416, 417, 419, 420, 615, 616, 617, 619, 620, 622, 623, 818, 819, 820, 822, 823, 826, 1021, 1023, 1025, 1026, 1028, 1029, 1224, 1225, 1226, 1229, 1231, 1232, 1427, 1428, 1429, 1630, 1631, 1632, 1833, 1838, 2036, 3254, 3255, 3256, 3318, 3457, 3458, 3459, 3660, 3918, 4268] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 1, 3], [1, 1, 0, 1], [2, 3, 2, 2], [0, 0, 3, 3]]», by decideFin!⟩
