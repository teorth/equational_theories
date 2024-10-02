
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 1, 3], [1, 2, 2, 0], [0, 3, 0, 2], [2, 1, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 1, 3], [1, 2, 2, 0], [0, 3, 0, 2], [2, 1, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 1, 3], [1, 2, 2, 0], [0, 3, 0, 2], [2, 1, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 1, 3], [1, 2, 2, 0], [0, 3, 0, 2], [2, 1, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [264, 614, 826, 2847, 3254] [3, 8, 23, 47, 99, 151, 203, 308, 309, 310, 312, 313, 315, 316, 323, 325, 326, 332, 333, 335, 336, 359, 411, 615, 617, 818, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2876, 3050, 3319, 3456, 3659, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 1, 3], [1, 2, 2, 0], [0, 3, 0, 2], [2, 1, 3, 1]]», by decideFin!⟩
