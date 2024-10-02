
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1853, 1855, 1863, 1865, 3693, 4092, 4094, 4591, 4609] [8, 99, 361, 362, 364, 365, 375, 377, 378, 385, 411, 817, 1020, 1223, 1833, 1837, 1838, 1840, 1841, 1848, 1858, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 3253, 3664, 3667, 3668, 3674, 3675, 3678, 3712, 3714, 3719, 3721, 3722, 3724, 3725, 3748, 3749, 3751, 3752, 3759, 3761, 3824, 3862, 4081] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 1], [2, 3, 0, 0], [2, 2, 3, 2], [3, 3, 3, 3]]», by decideFin!⟩
