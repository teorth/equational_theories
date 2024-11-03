
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [473, 3271] [513, 1278, 1325, 2043, 3278, 3306, 3456, 3659, 3962, 4275, 4320] :=
    ⟨Fin 4, «FinitePoly [[2,1,0,3],[2,1,3,0],[2,1,0,3],[2,0,1,3]]», Finite.of_fintype _, by decideFin!⟩
