
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 0, 0, 3], [0, 3, 3, 1], [0, 3, 3, 2], [3, 1, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 0, 0, 3], [0, 3, 3, 1], [0, 3, 3, 2], [3, 1, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 0, 0, 3], [0, 3, 3, 1], [0, 3, 3, 2], [3, 1, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 0, 0, 3], [0, 3, 3, 1], [0, 3, 3, 2], [3, 1, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [430] [3, 14, 23, 47, 99, 151, 203, 255, 307, 359, 417, 439, 466, 477, 501, 510, 614, 817, 1023, 1036, 1038, 1073, 1075, 1109, 1113, 1223, 1426, 1629, 1841, 1848, 1860, 1888, 1894, 1924, 1932, 2035, 2238, 2441, 2644, 2847, 3050, 3259, 3272, 3281, 3308, 3343, 3352, 3456, 3659, 3865, 3878, 3880, 3917, 3951, 3955, 4065, 4273, 4290, 4380, 4588, 4605] :=
    ⟨Fin 4, «FinitePoly [[1, 0, 0, 3], [0, 3, 3, 1], [0, 3, 3, 2], [3, 1, 0, 0]]», by decideFin!⟩
