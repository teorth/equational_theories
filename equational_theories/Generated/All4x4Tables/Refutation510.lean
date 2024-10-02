
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 2, 1, 3], [0, 1, 3, 2], [3, 1, 2, 0], [1, 0, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 2, 1, 3], [0, 1, 3, 2], [3, 1, 2, 0], [1, 0, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 2, 1, 3], [0, 1, 3, 2], [3, 1, 2, 0], [1, 0, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 2, 1, 3], [0, 1, 3, 2], [3, 1, 2, 0], [1, 0, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [72, 127, 179, 270, 315, 500, 703, 909, 916, 1075, 1238, 1325, 1525, 2087, 2137, 2696, 2899, 3484, 3687, 4409] [117, 159, 260, 385, 632, 825, 879, 1085, 1228, 1278, 1315, 1451, 1657, 1721, 1860, 2043, 2050, 2100, 2300, 2456, 2503, 2659, 2669, 2852, 2862, 2872, 3055, 3112, 3474, 3667, 3752, 3952, 4070, 4128, 4165, 4480, 4606] :=
    ⟨Fin 4, «FinitePoly [[0, 2, 1, 3], [0, 1, 3, 2], [3, 1, 2, 0], [1, 0, 2, 3]]», by decideFin!⟩
