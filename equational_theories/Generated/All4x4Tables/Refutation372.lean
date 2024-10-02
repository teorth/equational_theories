
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 0, 1], [2, 3, 1, 1], [2, 1, 2, 2], [1, 3, 0, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 0, 1], [2, 3, 1, 1], [2, 1, 2, 2], [1, 3, 0, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 0, 1], [2, 3, 1, 1], [2, 1, 2, 2], [1, 3, 0, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 0, 1], [2, 3, 1, 1], [2, 1, 2, 2], [1, 3, 0, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [427, 1020] [360, 361, 362, 364, 365, 367, 375, 377, 378, 385, 513, 1028, 1038, 1832, 3659, 4131] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 0, 1], [2, 3, 1, 1], [2, 1, 2, 2], [1, 3, 0, 2]]», by decideFin!⟩
