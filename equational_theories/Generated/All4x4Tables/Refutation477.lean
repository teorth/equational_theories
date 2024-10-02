
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 2, 0, 3], [3, 0, 2, 1], [2, 1, 3, 0], [0, 3, 1, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 2, 0, 3], [3, 0, 2, 1], [2, 1, 3, 0], [0, 3, 1, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 2, 0, 3], [3, 0, 2, 1], [2, 1, 3, 0], [0, 3, 1, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 2, 0, 3], [3, 0, 2, 1], [2, 1, 3, 0], [0, 3, 1, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [53, 66, 159, 170, 177, 273, 281, 1117, 1152, 1155, 2538, 2573, 2576, 4332, 4647] [3, 8, 23, 48, 49, 50, 52, 55, 56, 62, 63, 65, 72, 73, 99, 152, 153, 154, 156, 157, 160, 166, 167, 169, 176, 179, 203, 256, 257, 258, 260, 261, 263, 270, 271, 274, 280, 283, 307, 359, 411, 614, 817, 1045, 1082, 1122, 1223, 1426, 1629, 1832, 2035, 2238, 2447, 2449, 2470, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4275, 4380, 4585] :=
    ⟨Fin 4, «FinitePoly [[1, 2, 0, 3], [3, 0, 2, 1], [2, 1, 3, 0], [0, 3, 1, 2]]», by decideFin!⟩
