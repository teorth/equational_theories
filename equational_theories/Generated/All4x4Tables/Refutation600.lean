
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,1,3],[3,1,2,0],[3,1,2,0],[0,1,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,1,3],[3,1,2,0],[3,1,2,0],[0,1,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,1,3],[3,1,2,0],[3,1,2,0],[0,1,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,1,3],[3,1,2,0],[3,1,2,0],[0,1,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3007] [3253, 3664, 3674, 3677] :=
    ⟨Fin 4, «FinitePoly [[1,1,1,3],[3,1,2,0],[3,1,2,0],[0,1,1,2]]», Finite.of_fintype _, by decideFin!⟩
