
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1],[2,0,1],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,2,1],[2,0,1],[1,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[2,0,1],[1,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,2,1],[2,0,1],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [50, 107, 1996, 2063, 2100, 2152] [105, 108, 151, 411, 614, 817, 1022, 1023, 1035, 1036, 1038, 1039, 1045, 1046, 1048, 1049, 1075, 1082, 1085, 1112, 1224, 1225, 1228, 1229, 1238, 1239, 1241, 1242, 1249, 1251, 1252, 1285, 1288, 1315, 1322, 1631, 1632, 1634, 1644, 1654, 1657, 1681, 1684, 1691, 1694, 1721, 1728, 1834, 1837, 1838, 1840, 1847, 1851, 1860, 1894, 1897, 1921, 1924, 1931, 2037, 2040, 2050, 2060, 2087, 2127, 2134, 2441, 2644, 2847, 3050, 3253, 3456, 3667, 3724, 3725, 3862, 4065, 4268, 4269, 4272, 4275, 4284, 4291, 4314, 4320, 4396, 4398, 4399, 4433, 4435, 4436, 4470, 4472, 4473, 4583, 4584, 4585, 4587, 4598, 4599, 4606, 4629, 4635] :=
    ⟨Fin 3, «All4x4Tables [[0,2,1],[2,0,1],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
