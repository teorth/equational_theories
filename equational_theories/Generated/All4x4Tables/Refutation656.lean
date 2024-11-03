
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,4,5,0],[1,1,0,0,1,0],[3,2,2,2,2,4],[3,3,1,3,3,4],[4,4,0,0,4,1],[2,2,5,5,5,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,4,5,0],[1,1,0,0,1,0],[3,2,2,2,2,4],[3,3,1,3,3,4],[4,4,0,0,4,1],[2,2,5,5,5,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,2,0,4,5,0],[1,1,0,0,1,0],[3,2,2,2,2,4],[3,3,1,3,3,4],[4,4,0,0,4,1],[2,2,5,5,5,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,4,5,0],[1,1,0,0,1,0],[3,2,2,2,2,4],[3,3,1,3,3,4],[4,4,0,0,4,1],[2,2,5,5,5,5]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1032] [616, 825, 3318, 4131] :=
    ⟨Fin 6, «FinitePoly [[0,2,0,4,5,0],[1,1,0,0,1,0],[3,2,2,2,2,4],[3,3,1,3,3,4],[4,4,0,0,4,1],[2,2,5,5,5,5]]», Finite.of_fintype _, by decideFin!⟩
