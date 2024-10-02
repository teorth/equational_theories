
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 1], [3, 2, 0, 0], [1, 1, 1, 1], [1, 0, 1, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 1], [3, 2, 0, 0], [1, 1, 1, 1], [1, 0, 1, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 1], [3, 2, 0, 0], [1, 1, 1, 1], [1, 0, 1, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 1], [3, 2, 0, 0], [1, 1, 1, 1], [1, 0, 1, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 152, 156, 1442, 1446, 1838, 1868, 3457, 3511, 3518, 3521, 4067, 4127, 4131, 4314] [153, 1435, 1448, 1629, 1869, 3253, 3459, 3462, 3465, 3522, 4118] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 1], [3, 2, 0, 0], [1, 1, 1, 1], [1, 0, 1, 0]]», by decideFin!⟩
