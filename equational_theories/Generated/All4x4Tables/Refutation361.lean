
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 2, 1], [3, 1, 2, 0], [0, 1, 2, 3], [1, 3, 2, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 2, 1], [3, 1, 2, 0], [0, 1, 2, 3], [1, 3, 2, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 2, 1], [3, 1, 2, 0], [0, 1, 2, 3], [1, 3, 2, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 2, 1], [3, 1, 2, 0], [0, 1, 2, 3], [1, 3, 2, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [47, 117, 127, 179, 1832, 2043, 2100, 3952, 4065] [48, 49, 50, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 100, 101, 102, 104, 105, 107, 108, 114, 115, 118, 124, 125, 152, 153, 154, 156, 157, 159, 160, 166, 167, 169, 170, 176, 177, 411, 1860, 2124, 3887, 3915, 3962, 4118, 4128, 4435, 4470, 4480] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 2, 1], [3, 1, 2, 0], [0, 1, 2, 3], [1, 3, 2, 0]]», by decideFin!⟩
