
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [414, 3700, 3906, 4341] [412, 413, 416, 417, 419, 420, 426, 427, 429, 430, 436, 437, 439, 440, 463, 464, 466, 467, 473, 474, 476, 477, 500, 501, 503, 504, 510, 511, 513, 1020, 1832, 3915] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 1], [3, 1, 2, 3], [2, 3, 1, 0], [1, 3, 1, 1]]», by decideFin!⟩
