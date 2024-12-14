
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,1],[2,2,0],[1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,2,1],[2,2,0],[1,0,0]]» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[2,2,0],[1,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,2,1],[2,2,0],[1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1441, 1478, 1681, 1684, 1691, 1833, 1834, 1840, 2036, 2037, 3457] [47, 99, 151, 203, 255, 307, 359, 411, 614, 817, 1020, 1223, 1431, 1434, 1443, 1447, 1631, 1632, 1634, 1635, 1637, 1648, 1655, 1657, 1837, 1841, 1847, 1851, 1857, 1858, 1860, 1861, 1921, 2040, 2043, 2050, 2063, 2087, 2124, 2244, 2247, 2256, 2266, 2441, 2644, 2847, 3050, 3255, 3256, 3262, 3309, 3315, 3316, 3318, 3319, 3343, 3346, 3458, 3461, 3464, 3465, 3509, 3512, 3519, 3521, 3522, 3867, 3915, 3925, 3952, 4066, 4068, 4070, 4071, 4074, 4090, 4118, 4120, 4121, 4128, 4130, 4155, 4165, 4268, 4269, 4270, 4284, 4291, 4314, 4320, 4472, 4583, 4584, 4585, 4587, 4598, 4599, 4606, 4629] :=
    ⟨Fin 3, «All4x4Tables [[1,2,1],[2,2,0],[1,0,0]]», Finite.of_fintype _, by decideFin!⟩
