
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,2],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[0,0,2],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[0,0,2],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[0,0,2],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2273, 2571, 3197, 3519, 3749, 4105, 4128] [231, 1631, 1644, 1657, 1721, 2240, 2290, 2300, 2303, 2327, 2330, 2340, 2443, 2459, 2469, 2506, 2530, 2646, 2659, 2672, 2699, 2736, 3052, 3068, 3105, 3142, 3253, 3458, 3459, 3461, 3481, 3664, 3668, 3674, 4131, 4138, 4155, 4269, 4272, 4314, 4320, 4606, 4631] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[0,0,2],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
