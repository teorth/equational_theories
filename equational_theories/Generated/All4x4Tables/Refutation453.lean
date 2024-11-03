
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,1],[2,3,3,3],[3,0,0,0],[1,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,1],[2,3,3,3],[3,0,0,0],[1,2,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,1],[2,3,3,3],[3,0,0,0],[1,2,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,1],[2,3,3,3],[3,0,0,0],[1,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3056] [3079] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,1],[2,3,3,3],[3,0,0,0],[1,2,2,2]]», Finite.of_fintype _, by decideFin!⟩
