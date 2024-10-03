import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[1,0,3,1],[2,0,0,2],[1,3,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[1,0,3,1],[2,0,0,2],[1,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[1,0,3,1],[2,0,0,2],[1,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[1,0,3,1],[2,0,0,2],[1,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [442,446,450,454,458] [375,1629,1631,1634,1637,1640,2035,2037,3258,3261,3264,3928,4118,4121,4128,4599] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[1,0,3,1],[2,0,0,2],[1,3,3,1]]», by decideFin!⟩
