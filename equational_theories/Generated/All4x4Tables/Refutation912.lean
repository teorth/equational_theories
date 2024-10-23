
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0],[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0],[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0],[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0],[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1184] [411, 4275] :=
    ⟨Fin 8, «FinitePoly [[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0],[1,2,3,4,6,7,5,0],[7,0,1,2,3,6,4,5],[7,0,1,2,3,6,4,5],[1,2,3,4,6,7,5,0]]», Finite.of_fintype _, by decideFin!⟩
