
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [818, 836, 1225, 1228, 1242] [1020, 1224, 1229, 1238, 1239, 1241, 1248, 1249, 1251, 1252, 1834, 1847, 1851, 1857, 1860, 3253, 3659, 3864, 3865, 3867, 3925, 3928, 4066, 4067, 4068, 4070, 4071, 4131, 4269, 4270, 4314, 4583, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,1],[3,1,1,2],[1,2,2,2],[2,2,3,2]]», by decideFin!⟩
