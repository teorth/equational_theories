
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,4,1,0],[2,1,3,2,4],[3,4,2,0,1],[1,2,4,1,3],[4,3,1,4,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,4,1,0],[2,1,3,2,4],[3,4,2,0,1],[1,2,4,1,3],[4,3,1,4,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,4,1,0],[2,1,3,2,4],[3,4,2,0,1],[1,2,4,1,3],[4,3,1,4,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,4,1,0],[2,1,3,2,4],[3,4,2,0,1],[1,2,4,1,3],[4,3,1,4,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [633] [203, 255, 1426, 1629] :=
    ⟨Fin 5, «FinitePoly [[1,2,4,1,0],[2,1,3,2,4],[3,4,2,0,1],[1,2,4,1,3],[4,3,1,4,2]]», Finite.of_fintype _, by decideFin!⟩
