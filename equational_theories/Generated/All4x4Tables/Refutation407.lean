
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 3, 2, 1], [3, 0, 1, 3], [2, 2, 0, 2], [1, 1, 3, 0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 3, 2, 1], [3, 0, 1, 3], [2, 2, 0, 2], [1, 1, 3, 0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 3, 2, 1], [3, 0, 1, 3], [2, 2, 0, 2], [1, 1, 3, 0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 3, 2, 1], [3, 0, 1, 3], [2, 2, 0, 2], [1, 1, 3, 0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1459, 1523, 1673, 1746, 1865, 2132, 2282, 2474, 3700, 4497] [1442, 1481, 1887, 1934, 2041, 2043, 2051, 2090, 2135, 2137, 2239, 2240, 2241, 2243, 2244, 2247, 2253, 2256, 2257, 2263, 2264, 2266, 2290, 2291, 2293, 2294, 2300, 2301, 2303, 2304, 2327, 2328, 2330, 2331, 2337, 2338, 2340, 2530, 2534, 3050, 4398, 4405, 4408, 4435, 4442] :=
    ⟨Fin 4, «FinitePoly [[0, 3, 2, 1], [3, 0, 1, 3], [2, 2, 0, 2], [1, 1, 3, 0]]», by decideFin!⟩
