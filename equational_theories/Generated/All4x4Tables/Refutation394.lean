
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2443, 3055, 3075, 3256] [8, 23, 151, 203, 309, 326, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2457, 2470, 2644, 2847, 3319, 3456, 3659, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]», by decideFin!⟩
