
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 0, 1], [1, 2, 1, 1], [2, 2, 0, 2], [2, 3, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 0, 1], [1, 2, 1, 1], [2, 2, 0, 2], [2, 3, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 0, 1], [1, 2, 1, 1], [2, 2, 0, 2], [2, 3, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 0, 1], [1, 2, 1, 1], [2, 2, 0, 2], [2, 3, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [10, 100, 378, 839, 1023, 1224, 1226, 1260, 3864] [13, 361, 375, 412, 414, 416, 417, 419, 420, 427, 430, 439, 823, 832, 843, 1227, 1230, 1250, 1833, 1837, 1838, 3306, 3315, 3870, 3918, 4070, 4073, 4118, 4584, 4608] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 0, 1], [1, 2, 1, 1], [2, 2, 0, 2], [2, 3, 3, 1]]», by decideFin!⟩
