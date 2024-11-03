
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1670, 1673, 2485, 3083, 3091] [1426, 1731, 1832, 2238, 2496, 2530, 2543, 2644, 3105, 3139, 3152, 3269, 3271, 3278, 3456, 3662, 3665, 3677, 3759, 4065, 4270, 4273, 4320, 4622] :=
    ⟨Fin 4, «FinitePoly [[2,3,2,3],[3,2,3,2],[1,0,1,0],[0,1,0,1]]», Finite.of_fintype _, by decideFin!⟩
