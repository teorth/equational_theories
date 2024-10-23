
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,5,2,0,0],[2,5,4,1,0,0],[2,4,4,1,3,3],[2,4,4,2,0,0],[2,4,4,2,3,0],[1,4,4,1,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,5,2,0,0],[2,5,4,1,0,0],[2,4,4,1,3,3],[2,4,4,2,0,0],[2,4,4,2,3,0],[1,4,4,1,0,0]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,5,5,2,0,0],[2,5,4,1,0,0],[2,4,4,1,3,3],[2,4,4,2,0,0],[2,4,4,2,3,0],[1,4,4,1,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,5,2,0,0],[2,5,4,1,0,0],[2,4,4,1,3,3],[2,4,4,2,0,0],[2,4,4,2,3,0],[1,4,4,1,0,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1437] [4065] :=
    ⟨Fin 6, «FinitePoly [[1,5,5,2,0,0],[2,5,4,1,0,0],[2,4,4,1,3,3],[2,4,4,2,0,0],[2,4,4,2,3,0],[1,4,4,1,0,0]]», Finite.of_fintype _, by decideFin!⟩
