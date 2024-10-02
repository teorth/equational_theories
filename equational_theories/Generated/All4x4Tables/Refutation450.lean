
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 0, 0], [2, 3, 1, 1], [2, 2, 2, 2], [3, 3, 3, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 0, 0], [2, 3, 1, 1], [2, 2, 2, 2], [3, 3, 3, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 0, 0], [2, 3, 1, 1], [2, 2, 2, 2], [3, 3, 3, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 0, 0], [2, 3, 1, 1], [2, 2, 2, 2], [3, 3, 3, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 10, 100, 378, 433, 439, 834, 839, 840, 846, 854, 1023, 1227, 1230, 1250, 1260, 3315, 3864, 3870] [11, 13, 14, 16, 360, 361, 362, 364, 365, 367, 375, 377, 385, 412, 414, 416, 417, 419, 420, 436, 437, 440, 463, 464, 466, 467, 473, 474, 476, 477, 500, 501, 503, 504, 510, 511, 513, 849, 1252, 1833, 1835, 1837, 1838, 1840, 1841, 1848, 1851, 1857, 1858, 1860, 1861, 1884, 1885, 1887, 1888, 1894, 1895, 1897, 1898, 1921, 1922, 1924, 1925, 1931, 1932, 1934, 3659, 3873, 3928, 4066, 4067, 4068, 4070, 4071, 4073, 4074, 4080, 4083, 4084, 4090, 4091, 4093, 4118, 4120, 4121, 4127, 4128, 4130, 4155, 4157, 4158, 4164, 4165, 4167] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 0, 0], [2, 3, 1, 1], [2, 2, 2, 2], [3, 3, 3, 2]]», by decideFin!⟩
