
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [528, 562, 2182] [107, 413, 416, 417, 426, 440, 476, 477, 503, 504, 511, 614, 817, 1020, 1225, 1241, 1251, 1276, 1285, 1322, 1426, 1629, 1832, 2037, 2038, 2040, 2041, 2060, 2088, 2127, 2128, 2134, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3864, 3865, 3870, 3878, 3880, 3890, 3917, 3918, 3928, 3951, 3955, 3964, 4065, 4269, 4270, 4272, 4273, 4284, 4290, 4291, 4380, 4584, 4585, 4588, 4590, 4598, 4599, 4605, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]», Finite.of_fintype _, by decideFin!⟩
