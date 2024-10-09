
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,3],[1,1,1,1],[2,2,2,2],[2,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,2,2],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,3],[1,1,1,1],[2,2,2,2],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,2,2],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [841] [108, 414, 427, 430, 436, 437, 439, 440, 823, 842, 843, 845, 846, 1023, 1036, 1039, 1046, 1049, 1252, 1851, 1857, 1860, 1861, 3256, 3306, 3315, 3318, 3663, 3665, 3729, 3864, 3865, 3870, 4066, 4067, 4068, 4070, 4071, 4073, 4270, 4314, 4583, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,2,2],[2,3,3,3]]», by decideFin!⟩
