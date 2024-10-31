
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [168, 3532, 4001] [47, 99, 159, 203, 255, 411, 614, 817, 1020, 1223, 1431, 1434, 1435, 1441, 1442, 1445, 1451, 1454, 1488, 1515, 1516, 1519, 1525, 1629, 1832, 2037, 2038, 2040, 2041, 2043, 2044, 2060, 2063, 2090, 2091, 2127, 2128, 2134, 2238, 2441, 2644, 2847, 3050, 3253, 3458, 3459, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3518, 3519, 3545, 3546, 3548, 3549, 3555, 3558, 3659, 3865, 3867, 3868, 3870, 3871, 3878, 3881, 3887, 3888, 3890, 3917, 3925, 3927, 3928, 3951, 3954, 3961, 3962, 3964, 4065, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4588, 4590, 4591, 4598, 4599, 4605, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,0,2,0]]», Finite.of_fintype _, by decideFin!⟩
