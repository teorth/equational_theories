
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 0, 0], [2, 1, 1, 1], [1, 3, 2, 2], [1, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 0, 0], [2, 1, 1, 1], [1, 3, 2, 2], [1, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 0, 0], [2, 1, 1, 1], [1, 3, 2, 2], [1, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 0, 0], [2, 1, 1, 1], [1, 3, 2, 2], [1, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [325, 412, 1032, 3317, 3320, 3526, 3714, 4433] [9, 49, 50, 100, 101, 152, 205, 264, 308, 416, 417, 419, 420, 619, 620, 622, 623, 819, 820, 822, 823, 1021, 1023, 1025, 1028, 1224, 1225, 1228, 1232, 1428, 1429, 1630, 1631, 1833, 1837, 1838, 2036, 2063, 2064, 2243, 2246, 2443, 2446, 2646, 2670, 2673, 2852, 2866, 2876, 3059, 3069, 3076, 3078, 3255, 3256, 3457, 3458, 3660, 3864, 4127, 4268] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 0, 0], [2, 1, 1, 1], [1, 3, 2, 2], [1, 3, 3, 3]]», by decideFin!⟩
