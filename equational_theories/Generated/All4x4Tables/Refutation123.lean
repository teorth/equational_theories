
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,0,3],[2,1,0,3],[2,0,1,3],[2,1,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,0,3],[2,1,0,3],[2,0,1,3],[2,1,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,0,3],[2,1,0,3],[2,0,1,3],[2,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,0,3],[2,1,0,3],[2,0,1,3],[2,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1028, 1109, 1122, 1515, 1746, 1887, 2063, 2100, 2152] [151, 411, 614, 817, 1023, 1035, 1036, 1038, 1045, 1049, 1075, 1082, 1085, 1112, 1228, 1238, 1288, 1315, 1434, 1451, 1488, 1634, 1657, 1681, 1691, 1721, 1840, 1847, 1860, 1897, 1921, 2037, 2038, 2040, 2041, 2050, 2060, 2087, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3667, 3712, 3752, 3759, 3862, 4065, 4269, 4270, 4275, 4283, 4284, 4320, 4396, 4435, 4442, 4473, 4480, 4584, 4585, 4587, 4598, 4599, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[1,2,0,3],[2,1,0,3],[2,0,1,3],[2,1,0,3]]», Finite.of_fintype _, by decideFin!⟩
