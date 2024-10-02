
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 2, 2, 3], [3, 3, 3, 2], [0, 1, 0, 0], [1, 0, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 2, 2, 3], [3, 3, 3, 2], [0, 1, 0, 0], [1, 0, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 2, 2, 3], [3, 3, 3, 2], [0, 1, 0, 0], [1, 0, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 2, 2, 3], [3, 3, 3, 2], [0, 1, 0, 0], [1, 0, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [209, 1453, 3091, 3460] [3, 8, 23, 47, 99, 159, 205, 255, 307, 359, 411, 614, 817, 1020, 1223, 1454, 1455, 1630, 1631, 1632, 1654, 1655, 1657, 1658, 1832, 2035, 2238, 2441, 2644, 2847, 3053, 3058, 3066, 3075, 3254, 3255, 3315, 3316, 3318, 3319, 3518, 3519, 3522, 3659, 3862, 4065, 4380, 4585] :=
    ⟨Fin 4, «FinitePoly [[2, 2, 2, 3], [3, 3, 3, 2], [0, 1, 0, 0], [1, 0, 1, 1]]», by decideFin!⟩
