
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0],[1,2,1],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0],[1,2,1],[2,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[1,0,0],[1,2,1],[2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0],[1,2,1],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [100, 361, 433, 839] [105, 108, 436, 437, 440, 835, 840, 842, 845, 846, 1036, 1039, 1046, 1049, 1227, 1239, 1242, 1250, 1252, 1851, 1857, 1860, 1861, 3256, 3278, 3279, 3318, 3659, 3865, 3878, 3881, 3887, 3888, 3928, 4066, 4067, 4068, 4071, 4083, 4084, 4090, 4091, 4093, 4270, 4293, 4314, 4583, 4591, 4598, 4606, 4622, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[1,0,0],[1,2,1],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
