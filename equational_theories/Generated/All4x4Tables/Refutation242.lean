
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1853, 1863, 3322, 4316] [8, 23, 40, 99, 151, 203, 307, 359, 411, 817, 1020, 1223, 1426, 1629, 1833, 1835, 1837, 1838, 1840, 1841, 1848, 1851, 1858, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 2238, 2441, 3050, 3254, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3308, 3309, 3315, 3318, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3456, 3543, 3659, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4081, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4270, 4284, 4314, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658, 4683, 4688] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 0, 3], [2, 3, 0, 3], [2, 1, 0, 1], [0, 1, 0, 1]]», by decideFin!⟩
