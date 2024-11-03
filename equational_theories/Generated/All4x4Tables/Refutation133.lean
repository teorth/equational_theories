
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,1,0],[1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[2,1,0],[1,2,2]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[2,1,0],[1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[2,1,0],[1,2,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [160, 362, 1454, 2044, 2264, 2653, 2850, 3079, 3668, 4383] [1451, 2053, 2064, 2240, 2254, 2853, 2863, 3259, 3261, 3306, 3308, 3462, 3511, 3660, 3661, 3662, 3664, 3665, 4066, 4067, 4070, 4074, 4128, 4268, 4270, 4283, 4396, 4398, 4433, 4435, 4473, 4598, 4631] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[2,1,0],[1,2,2]]», Finite.of_fintype _, by decideFin!⟩
