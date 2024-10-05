
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2716, 3108] [107, 124, 127, 159, 413, 416, 419, 426, 429, 436, 439, 466, 473, 476, 503, 513, 1041, 1048, 1055, 1075, 1082, 1085, 1109, 1112, 1119, 1122, 1231, 1241, 1251, 1278, 1285, 1288, 1312, 1315, 1322, 1637, 1657, 1694, 1721, 1728, 1731, 1834, 1840, 1860, 1887, 1897, 1924, 1931, 1958, 2037, 2043, 2053, 2060, 2063, 2097, 2100, 2127, 2134, 2137, 2296, 2310, 2314, 2318, 2347, 2364, 2368, 2372, 2381, 2398, 2584, 2665, 2669, 2699, 2739, 3255, 3258, 3261, 3268, 3271, 3278, 3281, 3529, 3749, 3883, 3890, 3897, 3918, 3925, 3928, 3952, 3955, 3962, 4073, 4083, 4093, 4121, 4131, 4158, 4165, 4269, 4272, 4275, 4362, 4590, 4599, 4606, 4677] :=
    ⟨Fin 4, «FinitePoly [[0,2,2,3],[2,1,2,3],[0,1,2,0],[0,1,1,3]]», by decideFin!⟩
