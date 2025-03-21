
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]» : Magma (Fin 8) where
  op := finOpTable "[[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1083, 1085] [99, 151, 255, 411, 615, 623, 633, 646, 670, 677, 817, 1021, 1028, 1029, 1035, 1036, 1038, 1039, 1045, 1049, 1075, 1076, 1112, 1223, 1427, 1435, 1445, 1486, 1516, 1629, 1832, 2035, 2247, 2257, 2264, 2301, 2459, 2460, 2466, 2497, 2504, 2506, 2531, 2646, 2659, 2670, 2696, 2700, 2734, 2849, 2852, 2873, 2903, 2910, 2937, 2946, 3055, 3065, 3076, 3149, 3253, 3457, 3458, 3461, 3465, 3475, 3512, 3519, 3521, 3555, 3660, 3662, 3665, 3668, 3674, 3677, 3678, 3684, 3685, 3714, 3721, 3724, 3725, 3749, 3761, 3862, 4065, 4268, 4269, 4270, 4275, 4284, 4290, 4303, 4314, 4320, 4408, 4436, 4443, 4472, 4479, 4583, 4584, 4587, 4588, 4590, 4591, 4598, 4599, 4606, 4608, 4629, 4636, 4658] :=
    ⟨Fin 8, «All4x4Tables [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]», Finite.of_fintype _, by decideFin!⟩
