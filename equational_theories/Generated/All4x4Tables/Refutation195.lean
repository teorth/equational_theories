
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 1, 1], [3, 0, 1, 1], [3, 1, 0, 2], [3, 0, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 1, 1], [3, 0, 1, 1], [3, 1, 0, 2], [3, 0, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 1, 1], [3, 0, 1, 1], [3, 1, 0, 2], [3, 0, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 1, 1], [3, 0, 1, 1], [3, 1, 0, 2], [3, 0, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [47, 822, 842, 3877] [3, 8, 23, 48, 49, 50, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 99, 151, 203, 255, 307, 359, 411, 614, 818, 819, 820, 823, 825, 826, 832, 833, 835, 836, 843, 845, 846, 869, 870, 872, 873, 879, 880, 882, 883, 906, 907, 909, 910, 916, 917, 919, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3864, 3865, 3867, 3868, 3870, 3871, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4065, 4275, 4276, 4284, 4380, 4584, 4591, 4606] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 1, 1], [3, 0, 1, 1], [3, 1, 0, 2], [3, 0, 0, 1]]», by decideFin!⟩
