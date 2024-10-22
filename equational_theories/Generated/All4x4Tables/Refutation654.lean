
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,1,0,3,0,0],[1,5,5,1,3,2,1],[0,1,4,4,3,5,3],[1,5,4,6,2,0,3],[2,2,3,2,2,2,3],[2,5,0,5,3,0,5],[1,5,3,3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,1,0,3,0,0],[1,5,5,1,3,2,1],[0,1,4,4,3,5,3],[1,5,4,6,2,0,3],[2,2,3,2,2,2,3],[2,5,0,5,3,0,5],[1,5,3,3,3,0,3]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[1,2,1,0,3,0,0],[1,5,5,1,3,2,1],[0,1,4,4,3,5,3],[1,5,4,6,2,0,3],[2,2,3,2,2,2,3],[2,5,0,5,3,0,5],[1,5,3,3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,1,0,3,0,0],[1,5,5,1,3,2,1],[0,1,4,4,3,5,3],[1,5,4,6,2,0,3],[2,2,3,2,2,2,3],[2,5,0,5,3,0,5],[1,5,3,3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3352] [3456, 3862, 4380] :=
    ⟨Fin 7, «FinitePoly [[1,2,1,0,3,0,0],[1,5,5,1,3,2,1],[0,1,4,4,3,5,3],[1,5,4,6,2,0,3],[2,2,3,2,2,2,3],[2,5,0,5,3,0,5],[1,5,3,3,3,0,3]]», Finite.of_fintype _, by decideFin!⟩
