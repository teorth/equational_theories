
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 0, 1], [3, 2, 1, 0], [3, 2, 1, 0], [3, 1, 2, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 0, 1], [3, 2, 1, 0], [3, 2, 1, 0], [3, 1, 2, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 0, 1], [3, 2, 1, 0], [3, 2, 1, 0], [3, 1, 2, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 0, 1], [3, 2, 1, 0], [3, 2, 1, 0], [3, 1, 2, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [473, 513, 1832, 2035, 4065] [8, 99, 179, 359, 412, 413, 414, 416, 417, 419, 420, 426, 427, 429, 430, 436, 437, 439, 440, 463, 464, 466, 467, 474, 476, 477, 500, 501, 503, 504, 510, 511, 1020, 1223, 1629, 1847, 2128, 3253, 3887, 3915, 4118, 4155] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 0, 1], [3, 2, 1, 0], [3, 2, 1, 0], [3, 1, 2, 0]]», by decideFin!⟩
