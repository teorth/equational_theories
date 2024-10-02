
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1, 1, 3, 1], [2, 1, 3, 2], [0, 1, 1, 3], [0, 1, 2, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1, 1, 3, 1], [2, 1, 3, 2], [0, 1, 1, 3], [0, 1, 2, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1, 1, 3, 1], [2, 1, 3, 2], [0, 1, 1, 3], [0, 1, 2, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1, 1, 3, 1], [2, 1, 3, 2], [0, 1, 1, 3], [0, 1, 2, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [280, 316, 2466, 3007, 3297] [256, 257, 258, 260, 261, 263, 264, 270, 271, 273, 274, 281, 283, 308, 309, 313, 315, 323, 325, 326, 333, 335, 2496, 2530, 2543, 2848, 2849, 2850, 2852, 2853, 2855, 2856, 2862, 2863, 2865, 2866, 2873, 2875, 2876, 2900, 2902, 2903, 2909, 2910, 2912, 2913, 2936, 2937, 2939, 2940, 2947, 2949, 3255, 3259, 3271, 3279, 3306, 3456] :=
    ⟨Fin 4, «FinitePoly [[1, 1, 3, 1], [2, 1, 3, 2], [0, 1, 1, 3], [0, 1, 2, 1]]», by decideFin!⟩
