
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,1,0],[2,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[1,1,0],[2,2,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[1,1,0],[2,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[1,1,0],[2,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1053, 1271, 3322, 3724, 3925, 4673] [426, 427, 429, 430, 832, 833, 836, 1035, 1038, 1048, 1238, 1834, 1847, 1851, 1860, 3278, 3279, 3306, 3318, 3660, 3661, 3665, 3677, 3684, 3685, 3687, 3864, 3865, 3867, 3878, 3881, 3887, 3888, 4065, 4269, 4293, 4314, 4583, 4591, 4606, 4608, 4622, 4631, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[1,1,0],[2,2,1]]», Finite.of_fintype _, by decideFin!⟩
