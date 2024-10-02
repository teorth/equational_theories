
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 0, 1], [1, 1, 0, 0], [2, 3, 2, 2], [3, 0, 0, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 0, 1], [1, 1, 0, 0], [2, 3, 2, 2], [3, 0, 0, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 0, 1], [1, 1, 0, 0], [2, 3, 2, 2], [3, 0, 0, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 0, 1], [1, 1, 0, 0], [2, 3, 2, 2], [3, 0, 0, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 9, 23, 48, 49, 50, 102, 152, 203, 255, 307, 359, 425, 628, 821, 823, 825, 826, 1021, 1023, 1032, 1224, 1236, 1427, 1428, 1429, 1630, 1632, 1833, 1837, 1838, 2036, 2249, 2443, 2449, 2646, 2852, 3257, 3318, 3459, 3660, 3715, 3722, 3864, 3918, 4395, 4470] [827, 829, 4127, 4131] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 0, 1], [1, 1, 0, 0], [2, 3, 2, 2], [3, 0, 0, 3]]», by decideFin!⟩
