import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2260] [160,212,1454,1455,1456,2264,2267,2270,3519,3521,4314] :=
    ⟨Fin 4, «FinitePoly [[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]», by decideFin!⟩
