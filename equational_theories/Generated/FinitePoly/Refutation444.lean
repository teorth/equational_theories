
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 2 * x + 0 * y + 2 * x * y) % 3' (0, 150, 155, 158, 1831, 1836, 1846, 1856, 1866, 4064, 4066)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3» : Magma (Fin 3) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + 2 * x + 2 * x * y

/-! The facts -/
theorem «Facts from FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 156, 159, 1832, 4067] [2, 3, 8, 23, 38, 39, 40, 43, 47, 99, 152, 153, 154, 157, 160, 166, 167, 169, 170, 176, 177, 179, 203, 255, 307, 331, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1833, 1834, 1835, 1838, 1840, 1841, 1848, 1850, 1851, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3337, 3456, 3543, 3659, 3862, 4055, 4066, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4258, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 3, «FinitePoly 2 * x² + 2 * y² + 2 * x + 2 * x * y % 3», by decideFin!⟩
