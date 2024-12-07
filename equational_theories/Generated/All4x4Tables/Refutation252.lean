
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,1],[2,2,1],[2,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[1,0,1],[2,2,1],[2,0,0]]» : Magma (Fin 3) where
  op := finOpTable "[[1,0,1],[2,2,1],[2,0,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[1,0,1],[2,2,1],[2,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [416, 1884, 1894, 2093, 2097, 3952] [99, 151, 413, 419, 426, 429, 436, 466, 473, 476, 503, 513, 1025, 1028, 1035, 1038, 1045, 1048, 1075, 1082, 1085, 1109, 1112, 1122, 1223, 1426, 1629, 1834, 1837, 1840, 1847, 1857, 1860, 1887, 1897, 1921, 1924, 1931, 2040, 2043, 2050, 2053, 2060, 2063, 2124, 2127, 2134, 3255, 3261, 3268, 3271, 3278, 3281, 3309, 3316, 3343, 3346, 3353, 3864, 3867, 3870, 3877, 3880, 3887, 3890, 3918, 3928, 3962, 4065, 4269, 4272, 4275, 4284, 4291, 4320, 4584, 4590, 4599, 4606, 4635] :=
    ⟨Fin 3, «All4x4Tables [[1,0,1],[2,2,1],[2,0,0]]», Finite.of_fintype _, by decideFin!⟩
