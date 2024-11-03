
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,0,0],[1,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[1,0,0],[1,1,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[1,0,0],[1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[1,0,0],[1,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3910] [359, 3253, 3724, 3865, 3887, 3915, 3925, 3928, 4066, 4067, 4070, 4071, 4073, 4081, 4083, 4084, 4091, 4093, 4131, 4269, 4293, 4314, 4583, 4591, 4598, 4606, 4608, 4631, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[1,0,0],[1,1,0]]», Finite.of_fintype _, by decideFin!⟩
