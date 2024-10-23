
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[0,0,1],[2,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,2],[0,0,1],[2,1,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,2],[0,0,1],[2,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,2],[0,0,1],[2,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3315, 3346, 3509, 3558, 4120, 4165] [3319, 3353, 3522, 3915, 3955, 3962, 4118, 4127, 4131, 4158, 4290, 4320, 4598] :=
    ⟨Fin 3, «FinitePoly [[0,0,2],[0,0,1],[2,1,2]]», Finite.of_fintype _, by decideFin!⟩
