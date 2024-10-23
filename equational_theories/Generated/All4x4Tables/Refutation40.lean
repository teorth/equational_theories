
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,4,2,2,1,6,0,0],[2,3,2,4,3,6,1,1],[2,2,2,2,2,2,2,2],[4,2,2,0,0,6,3,3],[0,1,2,3,5,6,5,6],[4,4,2,4,6,4,4,6],[1,3,2,0,5,4,7,6],[1,3,2,0,6,6,6,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,4,2,2,1,6,0,0],[2,3,2,4,3,6,1,1],[2,2,2,2,2,2,2,2],[4,2,2,0,0,6,3,3],[0,1,2,3,5,6,5,6],[4,4,2,4,6,4,4,6],[1,3,2,0,5,4,7,6],[1,3,2,0,6,6,6,6]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,4,2,2,1,6,0,0],[2,3,2,4,3,6,1,1],[2,2,2,2,2,2,2,2],[4,2,2,0,0,6,3,3],[0,1,2,3,5,6,5,6],[4,4,2,4,6,4,4,6],[1,3,2,0,5,4,7,6],[1,3,2,0,6,6,6,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,4,2,2,1,6,0,0],[2,3,2,4,3,6,1,1],[2,2,2,2,2,2,2,2],[4,2,2,0,0,6,3,3],[0,1,2,3,5,6,5,6],[4,4,2,4,6,4,4,6],[1,3,2,0,5,4,7,6],[1,3,2,0,6,6,6,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3352] [4065, 4380] :=
    ⟨Fin 8, «FinitePoly [[1,4,2,2,1,6,0,0],[2,3,2,4,3,6,1,1],[2,2,2,2,2,2,2,2],[4,2,2,0,0,6,3,3],[0,1,2,3,5,6,5,6],[4,4,2,4,6,4,4,6],[1,3,2,0,5,4,7,6],[1,3,2,0,6,6,6,6]]», Finite.of_fintype _, by decideFin!⟩
