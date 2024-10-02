
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 1, 3, 3], [3, 2, 0, 3], [3, 3, 0, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 1, 3, 3], [3, 2, 0, 3], [3, 3, 0, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 1, 3, 3], [3, 2, 0, 3], [3, 3, 0, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 1, 3, 3], [3, 2, 0, 3], [3, 3, 0, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [203, 283, 2243, 2246, 2256, 2609, 4591] [8, 204, 205, 206, 208, 209, 211, 212, 218, 219, 221, 222, 228, 229, 231, 256, 257, 258, 260, 261, 263, 264, 270, 271, 273, 274, 280, 281, 411, 1020, 1832, 2239, 2240, 2241, 2244, 2247, 2253, 2254, 2257, 2263, 2264, 2266, 2267, 2290, 2291, 2293, 2294, 2300, 2301, 2303, 2304, 2327, 2328, 2330, 2331, 2337, 2338, 2644, 3253, 3456, 3862, 4065] :=
    ⟨Fin 4, «FinitePoly [[2, 1, 3, 3], [3, 2, 0, 3], [3, 3, 0, 3], [0, 1, 2, 3]]», by decideFin!⟩
