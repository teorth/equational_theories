
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 2, 3], [2, 1, 0, 2], [2, 1, 0, 2], [0, 0, 2, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 2, 3], [2, 1, 0, 2], [2, 1, 0, 2], [0, 0, 2, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 2, 3], [2, 1, 0, 2], [2, 1, 0, 2], [0, 0, 2, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 2, 3], [2, 1, 0, 2], [2, 1, 0, 2], [0, 0, 2, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2300] [8, 23, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2327, 2441, 2644, 2847, 3050, 3253, 3456, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 2, 3], [2, 1, 0, 2], [2, 1, 0, 2], [0, 0, 2, 1]]», by decideFin!⟩
