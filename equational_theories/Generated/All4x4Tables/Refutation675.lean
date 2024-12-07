
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[4,2,3,1,0],[3,4,0,2,1],[1,3,4,0,2],[2,0,1,4,3],[0,1,2,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[4,2,3,1,0],[3,4,0,2,1],[1,3,4,0,2],[2,0,1,4,3],[0,1,2,3,4]]» : Magma (Fin 5) where
  op := finOpTable "[[4,2,3,1,0],[3,4,0,2,1],[1,3,4,0,2],[2,0,1,4,3],[0,1,2,3,4]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[4,2,3,1,0],[3,4,0,2,1],[1,3,4,0,2],[2,0,1,4,3],[0,1,2,3,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1537] [419, 427, 464, 504, 511, 513, 617, 639, 676, 716, 825, 833, 872, 906, 1023, 1045, 1082, 1109, 1122, 1231, 1239, 1278, 1285, 1289, 1312, 1434, 1444, 1451, 1479, 1632, 1645, 1654, 1691, 1722, 1838, 1840, 1887, 1921, 1925, 2043, 2053, 2060, 2064, 2088, 2137, 2241, 2244, 2254, 2263, 2267, 2293, 2338, 2444, 2447, 2449, 2470, 2530, 2647, 2660, 2669, 2699, 2853, 2855, 2936, 3075, 3079, 3103, 3105, 3116, 3143, 3261, 3269, 3306, 3342, 3346, 3353, 3355, 3459, 3481, 3518, 3545, 3556, 3558, 3667, 3675, 3714, 3748, 3752, 3761, 3865, 3887, 3924, 3951, 3962, 3964, 4073, 4081, 4120, 4127, 4131, 4154, 4167, 4275, 4283, 4290, 4362, 4396, 4398, 4405, 4442, 4473, 4585, 4605, 4635, 4673] :=
    ⟨Fin 5, «All4x4Tables [[4,2,3,1,0],[3,4,0,2,1],[1,3,4,0,2],[2,0,1,4,3],[0,1,2,3,4]]», Finite.of_fintype _, by decideFin!⟩
