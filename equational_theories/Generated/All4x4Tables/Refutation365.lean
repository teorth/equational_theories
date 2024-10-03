import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,3,1],[1,1,1,1],[1,2,1,2],[0,3,3,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,3,1],[1,1,1,1],[1,2,1,2],[0,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,0,3,1],[1,1,1,1],[1,2,1,2],[0,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,3,1],[1,1,1,1],[1,2,1,2],[0,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [834] [836] :=
    ⟨Fin 4, «FinitePoly [[0,0,3,1],[1,1,1,1],[1,2,1,2],[0,3,3,1]]», by decideFin!⟩
