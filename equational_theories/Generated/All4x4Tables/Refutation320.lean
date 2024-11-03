
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [416] [359, 1020, 1832, 2035, 3253, 3862] :=
    ⟨Fin 4, «FinitePoly [[2,2,0,3],[2,2,1,0],[2,2,0,3],[2,3,1,0]]», Finite.of_fintype _, by decideFin!⟩
