
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1797, 2182] [429, 473, 3271, 3346, 4320] :=
    ⟨Fin 4, «FinitePoly [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]», Finite.of_fintype _, by decideFin!⟩
