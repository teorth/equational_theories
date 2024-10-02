
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 1, 1], [3, 0, 0, 3], [0, 0, 3, 0], [2, 2, 2, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 1, 1], [3, 0, 0, 3], [0, 0, 3, 0], [2, 2, 2, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 1, 1], [3, 0, 0, 3], [0, 0, 3, 0], [2, 2, 2, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 1, 1], [3, 0, 0, 3], [0, 0, 3, 0], [2, 2, 2, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1633, 3521, 4268] [3, 8, 26, 29, 47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1426, 1654, 1658, 1832, 2035, 2238, 2443, 2446, 2449, 2457, 2467, 2470, 2644, 2847, 3053, 3056, 3058, 3066, 3068, 3075, 3079, 3253, 3457, 3458, 3459, 3518, 3659, 3862, 4068, 4071, 4073, 4120, 4127, 4131, 4314, 4380, 4585, 4598] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 1, 1], [3, 0, 0, 3], [0, 0, 3, 0], [2, 2, 2, 1]]», by decideFin!⟩
