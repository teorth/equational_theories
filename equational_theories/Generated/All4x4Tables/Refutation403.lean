
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,3,1],[3,2,3,1],[2,0,1,0],[2,0,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,3,1],[3,2,3,1],[2,0,1,0],[2,0,2,3]]» : Magma (Fin 4) where
  op := finOpTable "[[0,1,3,1],[3,2,3,1],[2,0,1,0],[2,0,2,3]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,3,1],[3,2,3,1],[2,0,1,0],[2,0,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [167] [56, 65, 66, 73, 75, 99, 159, 203, 261, 264, 274, 283, 411, 615, 616, 619, 620, 622, 623, 629, 630, 632, 633, 639, 640, 642, 643, 667, 669, 670, 676, 677, 679, 680, 704, 706, 707, 713, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2849, 2852, 2853, 2855, 2856, 2862, 2863, 2865, 2866, 2872, 2873, 2875, 2899, 2900, 2902, 2903, 2909, 2910, 2912, 2937, 2939, 2940, 2946, 2947, 2949, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4276, 4283, 4284, 4290, 4291, 4293, 4314, 4320, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4588, 4590, 4591, 4598, 4599, 4605, 4606, 4608, 4629, 4635, 4636, 4658] :=
    ⟨Fin 4, «All4x4Tables [[0,1,3,1],[3,2,3,1],[2,0,1,0],[2,0,2,3]]», Finite.of_fintype _, by decideFin!⟩
