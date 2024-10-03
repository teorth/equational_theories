import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,1,1],[3,1,1,1],[1,2,2,2],[2,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,1,1],[3,1,1,1],[1,2,2,2],[2,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,1,1],[3,1,1,1],[1,2,2,2],[2,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,1,1],[3,1,1,1],[1,2,2,2],[2,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3723,3724,3726,3727,3728,3730] [359,360,361,377,378,379,4065,4066,4067,4068,4069,4127,4128,4129,4130,4131,4132,4133,4134,4135,4136,4583,4597,4629,4630,4654,4672] :=
    ⟨Fin 4, «FinitePoly [[1,3,1,1],[3,1,1,1],[1,2,2,2],[2,3,3,3]]», by decideFin!⟩
