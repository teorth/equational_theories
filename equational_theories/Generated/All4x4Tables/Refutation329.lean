
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0], [1, 0, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0], [1, 0, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0], [1, 0, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0], [1, 0, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 1647, 1655, 1685, 1691, 1731, 3261, 3278, 3306, 3353, 4636, 4658] [8, 255, 411, 1020, 1638, 1719, 1780, 1832, 3271, 3319, 3346, 3414, 3862, 4275, 4320, 4591, 4608] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0], [1, 0, 3, 2]]», by decideFin!⟩
