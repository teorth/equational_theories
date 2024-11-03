
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,3,1,5],[2,2,3,3,4,5],[0,3,5,5,4,5],[0,1,5,5,4,4],[1,1,2,3,1,0],[0,1,2,4,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,3,1,5],[2,2,3,3,4,5],[0,3,5,5,4,5],[0,1,5,5,4,4],[1,1,2,3,1,0],[0,1,2,4,0,0]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,2,3,1,5],[2,2,3,3,4,5],[0,3,5,5,4,5],[0,1,5,5,4,4],[1,1,2,3,1,0],[0,1,2,4,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,3,1,5],[2,2,3,3,4,5],[0,3,5,5,4,5],[0,1,5,5,4,4],[1,1,2,3,1,0],[0,1,2,4,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2702] [211, 221, 231, 1629, 2256, 2266, 2293, 2300, 2303, 2330, 2340, 2443, 2449, 2456, 2459, 2466, 2469, 2496, 2506, 2530, 2533, 2543, 2652, 2659, 2662, 2672, 2709, 2736, 2746, 3050, 3253, 3456, 3659, 4065, 4269, 4272, 4320, 4606, 4622, 4631] :=
    ⟨Fin 6, «FinitePoly [[1,2,2,3,1,5],[2,2,3,3,4,5],[0,3,5,5,4,5],[0,1,5,5,4,4],[1,1,2,3,1,0],[0,1,2,4,0,0]]», Finite.of_fintype _, by decideFin!⟩
