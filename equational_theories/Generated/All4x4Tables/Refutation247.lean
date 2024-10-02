
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 2, 1], [3, 3, 3, 3], [3, 2, 3, 3], [0, 0, 0, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 2, 1], [3, 3, 3, 3], [3, 2, 3, 3], [0, 0, 0, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 2, 1], [3, 3, 3, 3], [3, 2, 3, 3], [0, 0, 0, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 2, 1], [3, 3, 3, 3], [3, 2, 3, 3], [0, 0, 0, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [257, 309, 2644, 2852, 2855, 2868, 3256, 3261, 3457, 3459] [3, 8, 23, 47, 99, 151, 203, 256, 258, 260, 261, 263, 264, 270, 271, 273, 274, 280, 281, 283, 308, 310, 312, 313, 315, 316, 323, 325, 326, 332, 333, 335, 336, 359, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2660, 2662, 2673, 2850, 2858, 2872, 2876, 3050, 3306, 3319, 3460, 3509, 3518, 3519, 3522, 3659, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 2, 1], [3, 3, 3, 3], [3, 2, 3, 3], [0, 0, 0, 0]]», by decideFin!⟩
