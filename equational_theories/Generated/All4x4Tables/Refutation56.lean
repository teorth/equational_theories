import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2540,3272,4343] [23,47,75,307,313,323,1629,1654,1694,1721,1832,1850,1897,1931,2449,2533,3050,3058,3068,3075,3259,3261,3456,3472,3484,3522,3546,3659,3678,4073,4118,4131,4146,4273,4332] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,3],[3,0,2,0],[0,3,3,2],[3,1,2,0]]», by decideFin!⟩
