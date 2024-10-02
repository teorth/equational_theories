
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [2, 3, 1, 2], [1, 2, 3, 1], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [2, 3, 1, 2], [1, 2, 3, 1], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [2, 3, 1, 2], [1, 2, 3, 1], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [2, 3, 1, 2], [1, 2, 3, 1], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [50, 368, 624, 3693, 4069, 4092, 4093, 4094, 4131] [48, 49, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 361, 365, 375, 616, 617, 619, 620, 629, 630, 632, 633, 639, 640, 642, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 3862, 4070, 4071, 4073, 4081, 4083, 4084, 4584, 4588, 4598, 4606, 4636] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [2, 3, 1, 2], [1, 2, 3, 1], [3, 3, 3, 3]]», by decideFin!⟩
