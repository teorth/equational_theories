
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2041] [2855] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,2,1,2],[1,1,2,1],[3,2,3,0]]», Finite.of_fintype _, by decideFin!⟩
