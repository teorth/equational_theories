
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2, 0, 2, 3], [3, 0, 2, 3], [0, 1, 2, 3], [1, 1, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2, 0, 2, 3], [3, 0, 2, 3], [0, 1, 2, 3], [1, 1, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2, 0, 2, 3], [3, 0, 2, 3], [0, 1, 2, 3], [1, 1, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2, 0, 2, 3], [3, 0, 2, 3], [0, 1, 2, 3], [1, 1, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2293, 2318, 2441, 2696, 2746] [2240, 2243, 2253, 2254, 2256, 2264, 2266, 2340, 2443, 2446, 2449, 2456, 2459, 2466, 2469, 2530, 3456, 4070, 4080, 4118, 4128] :=
    ⟨Fin 4, «FinitePoly [[2, 0, 2, 3], [3, 0, 2, 3], [0, 1, 2, 3], [1, 1, 2, 2]]», by decideFin!⟩
