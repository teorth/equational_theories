import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,3,0,1],[2,2,1,2],[2,2,2,2],[0,2,3,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,3,0,1],[2,2,1,2],[2,2,2,2],[0,2,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,3,0,1],[2,2,1,2],[2,2,2,2],[0,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,3,0,1],[2,2,1,2],[2,2,2,2],[0,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1251] [99,104,107,1225,1228,1241,1254,3256,3659,3662,3665,3862,3867,3870,4270,4341] :=
    ⟨Fin 4, «FinitePoly [[1,3,0,1],[2,2,1,2],[2,2,2,2],[0,2,3,0]]», by decideFin!⟩
