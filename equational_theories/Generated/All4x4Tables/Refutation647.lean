
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [826] [47, 99, 151, 203, 261, 263, 411, 619, 620, 622, 623, 629, 630, 632, 633, 639, 640, 642, 643, 819, 832, 833, 835, 836, 842, 843, 845, 1023, 1028, 1029, 1035, 1036, 1039, 1045, 1046, 1048, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2646, 2647, 2649, 2650, 2652, 2659, 2660, 2662, 2669, 2670, 2672, 2849, 2852, 2853, 2855, 2856, 2862, 2863, 2865, 2866, 2872, 2873, 2875, 3050, 3255, 3256, 3258, 3259, 3261, 3262, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3712, 3714, 3721, 3722, 3724, 3725, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]», Finite.of_fintype _, by decideFin!⟩
