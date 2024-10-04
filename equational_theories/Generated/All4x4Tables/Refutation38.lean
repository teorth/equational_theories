
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [417, 419, 620, 622, 1026, 1038, 1045, 1239, 1241, 1248, 3662, 3725] [8, 23, 99, 359, 413, 414, 426, 427, 429, 436, 437, 439, 440, 617, 632, 639, 643, 817, 1022, 1023, 1028, 1039, 1041, 1046, 1048, 1049, 1055, 1224, 1225, 1226, 1228, 1229, 1238, 1242, 1251, 1252, 1432, 1442, 1451, 1455, 1629, 1832, 1857, 2035, 2053, 2060, 2064, 2241, 2244, 2256, 2267, 2444, 2447, 2449, 2457, 2459, 2466, 2470, 2644, 2660, 2662, 2847, 3050, 3075, 3079, 3253, 3459, 3462, 3464, 3509, 3518, 3663, 3665, 3667, 3712, 3714, 3721, 3862, 3915, 3917, 4065, 4120, 4131, 4270, 4283, 4314, 4318, 4396, 4398, 4433, 4473, 4583, 4598, 4601, 4656, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]», by decideFin!⟩
