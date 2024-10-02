
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 1], [3, 3, 3, 2], [3, 3, 2, 0], [2, 0, 1, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 1], [3, 3, 3, 2], [3, 3, 2, 0], [2, 0, 1, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 1], [3, 3, 3, 2], [3, 3, 2, 0], [2, 0, 1, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 1], [3, 3, 3, 2], [3, 3, 2, 0], [2, 0, 1, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1426, 2125] [1427, 1428, 1429, 1431, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1451, 1452, 1454, 1455, 1478, 1479, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1528, 3456, 3863, 3864, 3865, 3867, 3868, 3870, 3871, 3877, 3878, 3880, 3881, 3887, 3888, 3890, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4065] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 1], [3, 3, 3, 2], [3, 3, 2, 0], [2, 0, 1, 1]]», by decideFin!⟩
