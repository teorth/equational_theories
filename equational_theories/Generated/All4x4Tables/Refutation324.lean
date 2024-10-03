import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2088,2089] [1426,1429,1479,1481,2051,2124,3456,3457,3461,3462,3463,3511,3512,3513,3521,3522,3523,3532,3533,3534,3535,3877,3880,3883,3915,3918,3921,3952,3955,3958,3989,3993,3997,4001,4314,4315,4339,4357,4587,4606,4615,4645,4666,4689] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,1,3,1],[2,0,2,0],[2,2,2,0]]», by decideFin!⟩
