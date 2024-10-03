import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[2,3,3,3],[0,1,3,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[2,3,3,3],[0,1,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[2,3,3,3],[0,1,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[2,3,3,3],[0,1,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4110] [4070,4071,4073,4075,4077,4078,4081,4082,4083,4084,4086,4088,4100,4102,4105,4106,4108,4109,4111,4114,4115] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[2,3,3,3],[0,1,3,3],[3,3,3,3]]», by decideFin!⟩
