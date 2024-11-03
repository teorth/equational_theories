
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,3,4,1],[2,1,1,1,1],[2,1,1,1,1],[1,1,1,1,1],[4,1,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,3,4,1],[2,1,1,1,1],[2,1,1,1,1],[1,1,1,1,1],[4,1,1,1,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,1,3,4,1],[2,1,1,1,1],[2,1,1,1,1],[1,1,1,1,1],[4,1,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,3,4,1],[2,1,1,1,1],[2,1,1,1,1],[1,1,1,1,1],[4,1,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3295, 3299] [3255, 3279, 4065, 4269, 4275, 4284, 4291, 4320, 4584, 4606] :=
    ⟨Fin 5, «FinitePoly [[1,1,3,4,1],[2,1,1,1,1],[2,1,1,1,1],[1,1,1,1,1],[4,1,1,1,1]]», Finite.of_fintype _, by decideFin!⟩
