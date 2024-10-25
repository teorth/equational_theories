
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]» : Magma (Fin 7) where
  op := memoFinOp fun x y => [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [124, 1924] [439, 1038, 1075, 1109, 1241, 1288, 1322, 1657, 1684, 1728, 1860, 1894, 2043, 2097, 3281, 3880, 4083, 4118, 4158] :=
    ⟨Fin 7, «FinitePoly [[2,1,0,5,3,4,6],[4,1,3,6,5,0,2],[2,6,0,1,4,5,3],[4,2,6,3,5,0,1],[5,2,6,0,4,3,1],[3,2,6,4,0,5,1],[4,3,1,2,5,0,6]]», Finite.of_fintype _, by decideFin!⟩
