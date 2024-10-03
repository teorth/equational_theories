import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1479,1480] [1481,1482,1483,1484,1485,1486,1487,2035,2036,2050,2051,2052,2087,2088,2089,2124,2125,2126,2161,2162,2163,2164,3457,3462,3463,3511,3512,3513,3521,3522,3523,3532,3533,3534,3535,3862,3864,3877,3880,3883,3915,3918,3921,3952,3955,3958,3989,3993,3997,4001,4268,4282,4314,4315,4339,4357,4606,4615,4645,4689] :=
    ⟨Fin 4, «FinitePoly [[0,2,0,1],[3,1,0,1],[3,1,3,1],[0,2,0,2]]», by decideFin!⟩
