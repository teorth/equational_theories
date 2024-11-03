
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[2,1,2],[1,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[2,1,2],[1,1,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[2,1,2],[1,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[2,1,2],[1,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [25, 156, 159, 616, 1234, 1654, 1657, 2043, 2070, 2691, 3081, 3732] [619, 1634, 1637, 2037, 2053, 2063, 2327, 2340, 2496, 2543, 2699, 2706, 2733, 2746, 2902, 2909, 2936, 2949, 3112, 3152, 3255, 3256, 3258, 3259, 3261, 3262, 3459, 3461, 3464, 3474, 3512, 3549, 3556, 3662, 3665, 3668, 3752, 3759, 3925, 4121, 4269, 4270, 4314, 4409, 4480, 4599] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[2,1,2],[1,1,2]]», Finite.of_fintype _, by decideFin!⟩
