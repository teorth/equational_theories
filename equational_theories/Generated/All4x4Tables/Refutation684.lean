
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,4,2,0,3],[2,5,4,1,3,0],[2,5,4,1,3,0],[1,5,4,2,0,3],[1,4,5,2,3,0],[1,4,5,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,4,2,0,3],[2,5,4,1,3,0],[2,5,4,1,3,0],[1,5,4,2,0,3],[1,4,5,2,3,0],[1,4,5,2,3,0]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,5,4,2,0,3],[2,5,4,1,3,0],[2,5,4,1,3,0],[1,5,4,2,0,3],[1,4,5,2,3,0],[1,4,5,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,4,2,0,3],[2,5,4,1,3,0],[2,5,4,1,3,0],[1,5,4,2,0,3],[1,4,5,2,3,0],[1,4,5,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [690, 1586] [47, 632, 642, 817, 1434, 3915, 3925, 3952, 3962, 4065, 4275, 4320] :=
    ⟨Fin 6, «FinitePoly [[1,5,4,2,0,3],[2,5,4,1,3,0],[2,5,4,1,3,0],[1,5,4,2,0,3],[1,4,5,2,3,0],[1,4,5,2,3,0]]», Finite.of_fintype _, by decideFin!⟩
