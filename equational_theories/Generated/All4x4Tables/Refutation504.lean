
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
  ∃ (G : Type) (_ : Magma G), Facts G [264, 307, 614, 826, 2847, 3254] [3, 8, 23, 47, 99, 151, 203, 283, 308, 309, 310, 312, 313, 315, 323, 325, 326, 333, 335, 359, 411, 615, 616, 617, 619, 620, 622, 623, 629, 630, 632, 633, 639, 640, 642, 643, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 818, 819, 820, 822, 823, 825, 832, 833, 835, 836, 842, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2876, 2902, 2912, 2949, 3050, 3319, 3456, 3659, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 1, 3], [1, 2, 2, 0], [0, 3, 0, 2], [2, 1, 3, 1]]», by decideFin!⟩
