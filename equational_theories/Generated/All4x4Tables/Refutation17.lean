import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,0,1],[0,3,2,3],[0,1,0,3],[0,3,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,0,1],[0,3,2,3],[0,1,0,3],[0,3,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,0,1],[0,3,2,3],[0,1,0,3],[0,3,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,0,1],[0,3,2,3],[0,1,0,3],[0,3,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [385,4209,4452] [375,395,3915,3925,3935,3952,3972,3989,4006,4023,4040,4118,4138,4155,4175,4192,4226,4243,4284,4287,4340,4360,4606,4615,4645,4689] :=
    ⟨Fin 4, «FinitePoly [[0,1,0,1],[0,3,2,3],[0,1,0,3],[0,3,2,3]]», by decideFin!⟩
