
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 3, 3], [2, 3, 2, 3], [1, 1, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 3, 3], [2, 3, 2, 3], [1, 1, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 3, 3], [2, 3, 2, 3], [1, 1, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 3, 3], [2, 3, 2, 3], [1, 1, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [25, 205, 211, 221, 1631, 1644, 1647, 2285, 2306, 2314, 2368, 2488, 2506, 2530, 2665, 2706, 2739, 2774, 3052, 3065, 3068, 3078, 3105, 3458, 3464, 3664, 3684, 3749, 4070, 4131, 4155, 4584] [31, 218, 231, 310, 312, 1637, 1657, 1718, 1721, 1731, 2340, 2696, 2746, 3058, 3139, 3152, 3256, 3258, 3261, 3262, 3268, 3269, 3272, 3278, 3537, 3604, 3674, 3722, 3759, 3824] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 3, 3], [2, 3, 2, 3], [1, 1, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
