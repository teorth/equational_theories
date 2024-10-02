
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 0, 1], [2, 1, 1, 2], [2, 2, 2, 2], [2, 0, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 0, 1], [2, 1, 1, 2], [2, 2, 2, 2], [2, 0, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 0, 1], [2, 1, 1, 2], [2, 2, 2, 2], [2, 0, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 0, 1], [2, 1, 1, 2], [2, 2, 2, 2], [2, 0, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [411, 1240, 1243, 1251] [107, 203, 359, 412, 413, 414, 416, 417, 419, 420, 426, 427, 429, 430, 436, 437, 439, 440, 463, 464, 466, 467, 473, 474, 476, 477, 500, 501, 503, 504, 510, 511, 513, 1020, 1225, 1249, 1262, 1426, 2441, 3659, 4065] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 0, 1], [2, 1, 1, 2], [2, 2, 2, 2], [2, 0, 3, 1]]», by decideFin!⟩
