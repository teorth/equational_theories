
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4229] [3306, 3308, 3353, 3355, 3511, 3518, 3549, 3556, 3917, 3924, 3955, 3962, 4127, 4131, 4154, 4158] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[3,1,2,3],[0,2,1,0],[1,3,0,1]]», Finite.of_fintype _, by decideFin!⟩
