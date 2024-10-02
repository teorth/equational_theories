
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 2, 1], [3, 2, 1, 2], [2, 1, 0, 3], [3, 0, 1, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 2, 1], [3, 2, 1, 2], [2, 1, 0, 3], [3, 0, 1, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 2, 1], [3, 2, 1, 2], [2, 1, 0, 3], [3, 0, 1, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 2, 1], [3, 2, 1, 2], [2, 1, 0, 3], [3, 0, 1, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [620, 2097, 3462, 3862] [419, 619, 622, 1036, 1038, 1861, 1894, 2041, 2051, 2060, 2090, 3261, 3306, 3459, 3461, 3464, 3509, 3511, 3518, 3522, 3659, 3865, 3917, 3955] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 2, 1], [3, 2, 1, 2], [2, 1, 0, 3], [3, 0, 1, 0]]», by decideFin!⟩
