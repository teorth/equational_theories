
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,1,4,3,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[3,2,1,4,3,4]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,1,4,3,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[3,2,1,4,3,4]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[3,2,1,4,3,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[3,2,1,4,3,4]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,1,4,3,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[3,2,1,4,3,4]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1697] [1931, 2134, 3880, 3890, 3952, 3962, 4073, 4093, 4606] :=
    ⟨Fin 6, «FinitePoly [[3,2,1,4,3,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[2,2,0,0,5,4],[3,2,1,0,5,4],[3,2,1,4,3,4]]», Finite.of_fintype _, by decideFin!⟩
