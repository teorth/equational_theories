
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,3,3],[0,0,0,0],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,3,3],[0,0,0,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,3,3],[0,0,0,0],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,3,3],[0,0,0,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [311, 4610] [3268, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3558, 3659, 3862, 4065, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4380, 4583, 4585, 4587, 4588, 4590, 4591, 4598, 4606, 4629, 4635, 4636] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,3,3],[0,0,0,0],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
