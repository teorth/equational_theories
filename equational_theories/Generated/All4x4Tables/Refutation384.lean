
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,3,3],[1,1,1,1],[2,2,2,2],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,3,3],[1,1,1,1],[2,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,3,3],[1,1,1,1],[2,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,3,3],[1,1,1,1],[2,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3933] [3258, 3259, 3261, 3262, 3306, 3308, 3309, 3461, 3462, 3464, 3465, 3509, 3511, 3512, 3664, 3665, 3667, 3668, 3712, 3714, 3867, 3868, 3870, 3871, 3915, 3917, 3918, 4070, 4071, 4073, 4074, 4118, 4120, 4121, 4269, 4270, 4283, 4284, 4398, 4399, 4433, 4470, 4598, 4599, 4631, 4656] :=
    ⟨Fin 4, «FinitePoly [[3,2,3,3],[1,1,1,1],[2,2,2,2],[3,3,3,3]]», Finite.of_fintype _, by decideFin!⟩
