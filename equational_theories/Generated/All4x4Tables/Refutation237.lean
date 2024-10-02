
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 1], [3, 2, 3, 2], [0, 0, 1, 0], [2, 2, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 1], [3, 2, 3, 2], [0, 0, 1, 0], [2, 2, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 1], [3, 2, 3, 2], [0, 0, 1, 0], [2, 2, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 1], [3, 2, 3, 2], [0, 0, 1, 0], [2, 2, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [151, 2036, 2050, 2060, 3862] [3, 8, 23, 47, 99, 152, 153, 154, 156, 157, 159, 160, 166, 167, 169, 170, 176, 177, 179, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2128, 2134, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3864, 3867, 3880, 3887, 3890, 3915, 3918, 3952, 3962, 4065, 4268, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 1], [3, 2, 3, 2], [0, 0, 1, 0], [2, 2, 0, 0]]», by decideFin!⟩
