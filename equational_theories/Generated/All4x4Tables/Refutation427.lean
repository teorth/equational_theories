
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 0, 2, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 0, 2, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 0, 2, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 0, 2, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 1480, 1481, 3877, 3918, 3955, 4587] [151, 359, 1428, 1429, 1435, 1442, 1444, 1445, 1482, 3456, 3864, 3865, 3867, 3868, 3870, 3871, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3925, 3927, 3928, 3951, 3952, 3954, 3961, 3962, 3964, 3993, 4065] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 3, 1], [3, 1, 3, 1], [2, 0, 2, 0], [2, 0, 2, 1]]», by decideFin!⟩
