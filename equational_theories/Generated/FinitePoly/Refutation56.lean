
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 0 * y**2 + 0 * x + 2 * y + 1 * x * y) % 3' (0, 150, 1425, 1831, 3455, 4064, 4130)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y + x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y + x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 2 * y + x * y % 3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [151, 1426, 1832, 3456, 4131] [47, 99, 154, 157, 159, 160, 167, 169, 170, 176, 177, 179, 203, 255, 359, 411, 614, 817, 1020, 1223, 1427, 1428, 1429, 1431, 1432, 1434, 1435, 1441, 1442, 1444, 1445, 1451, 1452, 1454, 1455, 1478, 1479, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1528, 1629, 1833, 1834, 1835, 1837, 1838, 1840, 1841, 1847, 1848, 1850, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3457, 3458, 3459, 3461, 3462, 3464, 3465, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly 2 * x² + 2 * y + x * y % 3», Finite.of_fintype _, by decideFin!⟩
