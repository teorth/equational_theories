
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 52, 361, 619, 635, 639, 3877, 3887, 4073, 4090] [8, 48, 49, 50, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 360, 362, 364, 365, 367, 375, 377, 378, 385, 411, 615, 617, 620, 622, 623, 630, 633, 640, 642, 643, 649, 666, 667, 669, 670, 676, 677, 679, 680, 703, 704, 706, 707, 713, 714, 716, 818, 819, 820, 823, 825, 826, 833, 835, 836, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1020, 1832, 2035, 3253, 3456, 3865, 3868, 3871, 3878, 3880, 3881, 3888, 3890, 3897, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4118, 4131] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]», by decideFin!⟩
