
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[7,3,1,3,4,3,3,3],[5,3,5,4,4,4,4,3],[7,6,1,4,4,3,3,6],[4,4,4,4,4,4,4,4],[4,4,4,4,4,4,4,4],[4,4,3,4,4,4,4,4],[3,4,3,4,4,4,4,4],[5,4,5,4,4,4,4,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[7,3,1,3,4,3,3,3],[5,3,5,4,4,4,4,3],[7,6,1,4,4,3,3,6],[4,4,4,4,4,4,4,4],[4,4,4,4,4,4,4,4],[4,4,3,4,4,4,4,4],[3,4,3,4,4,4,4,4],[5,4,5,4,4,4,4,4]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[7,3,1,3,4,3,3,3],[5,3,5,4,4,4,4,3],[7,6,1,4,4,3,3,6],[4,4,4,4,4,4,4,4],[4,4,4,4,4,4,4,4],[4,4,3,4,4,4,4,4],[3,4,3,4,4,4,4,4],[5,4,5,4,4,4,4,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[7,3,1,3,4,3,3,3],[5,3,5,4,4,4,4,3],[7,6,1,4,4,3,3,6],[4,4,4,4,4,4,4,4],[4,4,4,4,4,4,4,4],[4,4,3,4,4,4,4,4],[3,4,3,4,4,4,4,4],[5,4,5,4,4,4,4,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4679] [4673, 4677, 4684] :=
    ⟨Fin 8, «FinitePoly [[7,3,1,3,4,3,3,3],[5,3,5,4,4,4,4,3],[7,6,1,4,4,3,3,6],[4,4,4,4,4,4,4,4],[4,4,4,4,4,4,4,4],[4,4,3,4,4,4,4,4],[3,4,3,4,4,4,4,4],[5,4,5,4,4,4,4,4]]», Finite.of_fintype _, by decideFin!⟩
