
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [437] [413, 440, 817, 1023, 1036, 1039, 1046, 1049, 1224, 1226, 1229, 1239, 1242, 1249, 1252, 1835, 1851, 1861, 3256, 3315, 3318, 3660, 3661, 3665, 3721, 3724, 3862, 4066, 4067, 4068, 4070, 4071, 4073, 4269, 4270, 4314, 4583, 4598, 4631, 4673] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[1,2,1,1],[2,2,2,2],[2,0,3,3]]», by decideFin!⟩
