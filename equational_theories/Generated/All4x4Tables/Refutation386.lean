
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 1, 1], [3, 0, 3, 1], [2, 0, 3, 0], [2, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 1, 1], [3, 0, 3, 1], [2, 0, 3, 0], [2, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 1, 1], [3, 0, 3, 1], [2, 0, 3, 0], [2, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 1, 1], [3, 0, 3, 1], [2, 0, 3, 0], [2, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 49, 364, 614, 1431, 1434, 1447, 4067, 4083, 4316, 4587] [23, 48, 50, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 151, 203, 307, 360, 361, 362, 365, 367, 368, 374, 375, 377, 378, 384, 385, 615, 617, 620, 623, 629, 630, 632, 633, 639, 640, 642, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 1427, 1432, 1437, 1478, 1629, 1832, 2238, 2441, 3050, 3253, 3456, 3543, 3659, 3862, 4086, 4118, 4131, 4284] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 1, 1], [3, 0, 3, 1], [2, 0, 3, 0], [2, 2, 3, 1]]», by decideFin!⟩
