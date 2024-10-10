
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [440, 1525, 4093] [47, 359, 614, 817, 1023, 1036, 1049, 1226, 1229, 1239, 1252, 1434, 1444, 1861, 3256, 3315, 3665, 3721, 3865, 3870, 3880, 3887, 3928, 3955, 3962, 4068, 4071, 4083, 4158, 4270, 4598, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,0,1,2],[3,0,2,1],[2,0,3,1]]», by decideFin!⟩
