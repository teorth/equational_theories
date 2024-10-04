
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [10, 100, 361, 378, 433, 834, 839, 854, 1230, 1260] [105, 108, 414, 436, 437, 440, 835, 840, 842, 845, 846, 1036, 1039, 1046, 1049, 1227, 1239, 1242, 1250, 1252, 1835, 1851, 1857, 1860, 1861, 3256, 3318, 3659, 3865, 3928, 4066, 4067, 4068, 4071, 4270, 4293, 4314, 4583, 4598, 4606, 4636] :=
    ⟨Fin 4, «FinitePoly [[3,3,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,2]]», by decideFin!⟩
