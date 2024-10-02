
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 1, 1], [3, 1, 1, 1], [3, 2, 2, 2], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 1, 1], [3, 1, 1, 1], [3, 2, 2, 2], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 1, 1], [3, 1, 1, 1], [3, 2, 2, 2], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 1, 1], [3, 1, 1, 1], [3, 2, 2, 2], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [49, 621, 3662] [3, 8, 23, 48, 50, 99, 151, 203, 255, 307, 359, 411, 617, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3722, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 1, 1], [3, 1, 1, 1], [3, 2, 2, 2], [3, 3, 3, 3]]», by decideFin!⟩
