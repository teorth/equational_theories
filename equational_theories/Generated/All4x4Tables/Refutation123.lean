
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[1,0,0],[2,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[1,0,0],[2,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[1,0,0],[2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[1,0,0],[2,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [437, 1042, 1267] [108, 413, 819, 832, 833, 836, 845, 1046, 1053, 1224, 1229, 1242, 1249, 1851, 3255, 3279, 3306, 3318, 3660, 3661, 3685, 3687, 3724, 3865, 3881, 3888, 4066, 4071, 4084, 4091, 4293, 4314, 4583, 4591, 4598, 4608, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[1,0,0],[2,2,0]]», Finite.of_fintype _, by decideFin!⟩
