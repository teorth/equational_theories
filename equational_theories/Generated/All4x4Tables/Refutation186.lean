
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[2,1,2],[1,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[2,1,2],[1,2,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[2,1,2],[1,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[2,1,2],[1,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1645, 2041, 2241, 2447, 2485, 2647, 2850, 2855, 4143] [1432, 1434, 1635, 1637, 2038, 2043, 2459, 2466, 2652, 2865, 2872, 3259, 3261, 3308, 3462, 4270, 4283] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[2,1,2],[1,2,1]]», Finite.of_fintype _, by decideFin!⟩
