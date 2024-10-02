
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 52, 361, 619, 635, 639, 3877, 3887, 4073, 4090, 4584] [8, 55, 375, 378, 411, 615, 617, 620, 622, 623, 630, 633, 640, 642, 643, 649, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 835, 1020, 1832, 2035, 3253, 3456, 3897, 3915, 3925, 3928, 4109, 4118, 4131] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]», by decideFin!⟩
