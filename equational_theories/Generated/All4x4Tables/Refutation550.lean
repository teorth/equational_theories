
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,4,2],[4,3,3,3,3],[0,4,0,0,0],[1,1,4,1,1],[4,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,2,4,2],[4,3,3,3,3],[0,4,0,0,0],[1,1,4,1,1],[4,4,4,4,4]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[2,2,2,4,2],[4,3,3,3,3],[0,4,0,0,0],[1,1,4,1,1],[4,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,2,4,2],[4,3,3,3,3],[0,4,0,0,0],[1,1,4,1,1],[4,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1636] [1637, 1834, 1840, 2253, 2459, 3258, 3316, 3318, 3319, 3462, 4120, 4121, 4130, 4131, 4598, 4599, 4629] :=
    ⟨Fin 5, «FinitePoly [[2,2,2,4,2],[4,3,3,3,3],[0,4,0,0,0],[1,1,4,1,1],[4,4,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
