
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1083, 1085] [255, 411, 1029, 1039, 1045, 1075, 1110, 1629, 1832, 3253, 3862, 4275, 4320, 4591, 4608, 4636, 4658] :=
    ⟨Fin 8, «FinitePoly [[0,3,4,6,1,2,7,5],[4,2,0,1,6,3,5,7],[5,6,7,3,2,1,4,0],[1,7,6,4,0,5,3,2],[2,4,3,7,5,0,6,1],[7,1,5,2,3,6,0,4],[3,0,2,5,7,4,1,6],[6,5,1,0,4,7,2,3]]», Finite.of_fintype _, by decideFin!⟩
