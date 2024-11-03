
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,2],[0,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,2],[0,1,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,2],[0,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,2],[0,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2306, 2739, 3180] [221, 231, 1637, 1657, 1721, 1731, 2293, 2330, 2340, 2496, 2506, 2533, 2543, 2652, 2662, 2672, 3058, 3115, 3152, 3258, 3268, 3271, 3278, 3481, 3509, 3659, 4090, 4155, 4272, 4320, 4606, 4622] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,2],[0,1,1]]», Finite.of_fintype _, by decideFin!⟩
