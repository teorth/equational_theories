
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,0],[1,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[0,0,0],[1,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[0,0,0],[1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[0,0,0],[1,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [371, 3882, 3899, 4076, 4109, 4318] [3253, 3456, 3664, 3667, 3668, 3674, 3675, 3678, 3721, 3724, 3725, 3865, 3887, 3915, 3925, 3928, 3952, 3955, 3962, 4131, 4158, 4268, 4275, 4283, 4284, 4290, 4293, 4300, 4380, 4635, 4673] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[0,0,0],[1,2,0]]», Finite.of_fintype _, by decideFin!⟩
