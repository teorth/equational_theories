
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 1, 3], [3, 3, 3, 3], [0, 1, 0, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 1, 3], [3, 3, 3, 3], [0, 1, 0, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 1, 3], [3, 3, 3, 3], [0, 1, 0, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 1, 3], [3, 3, 3, 3], [0, 1, 0, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2672, 2709, 2746, 3152] [3, 8, 23, 47, 99, 151, 203, 255, 308, 309, 310, 312, 313, 315, 325, 326, 333, 335, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2647, 2669, 2673, 2707, 2734, 2736, 2847, 3053, 3058, 3059, 3066, 3075, 3078, 3079, 3106, 3112, 3142, 3150, 3259, 3272, 3281, 3308, 3319, 3343, 3352, 3456, 3659, 3862, 4065, 4273, 4290, 4380, 4588, 4605] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 1, 3], [3, 3, 3, 3], [0, 1, 0, 3], [0, 1, 2, 3]]», by decideFin!⟩
