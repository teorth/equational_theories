
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[0,0,1],[0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[0,0,1],[0,2,0]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[0,0,1],[0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[0,0,1],[0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [317, 3275] [3259, 3271, 3306, 3456, 3660, 3661, 3667, 3675, 3685, 3687, 3712, 3749, 3759, 3862, 4065, 4269, 4273, 4283, 4291, 4314, 4320, 4321, 4369, 4380, 4583, 4584, 4588, 4591, 4598, 4606, 4608, 4636, 4658] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[0,0,1],[0,2,0]]», Finite.of_fintype _, by decideFin!⟩
