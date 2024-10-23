
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[1,0,1],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2],[1,0,1],[2,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,1,2],[1,0,1],[2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2],[1,0,1],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2688, 3011, 3214, 4477] [2041, 2043, 2053, 2650, 2669, 2855, 2863, 2865, 2909, 2936, 3068, 3112, 3259, 3261, 3271, 3308, 3462, 3474, 3667, 4283, 4320, 4598] :=
    ⟨Fin 3, «FinitePoly [[0,1,2],[1,0,1],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
