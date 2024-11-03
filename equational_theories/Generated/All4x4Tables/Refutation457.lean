
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3304] [323, 359, 3456, 3660, 3661, 3667, 3675, 3685, 3687, 3862, 4066, 4067, 4070, 4071, 4073, 4081, 4083, 4084, 4091, 4093, 4268, 4269, 4273, 4275, 4283, 4284, 4290, 4293, 4300, 4314, 4320, 4321, 4380, 4583, 4584, 4588, 4591, 4598, 4606, 4608, 4636] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[3,3,3,3],[2,3,3,3],[1,2,3,3]]», Finite.of_fintype _, by decideFin!⟩
