
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
  ∃ (G : Type) (_ : Magma G), Facts G [1, 9, 102, 152, 823, 825, 826, 1032, 1224, 1236, 1630, 1632, 2036, 2443, 2449, 2646, 2852, 3459, 3660, 4395] [159, 827, 829, 1451, 1657, 1860, 2043, 2669, 3667, 4127, 4131] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 0, 1], [1, 1, 0, 0], [2, 3, 2, 2], [3, 0, 0, 3]]», by decideFin!⟩
