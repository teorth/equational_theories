import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3],[1,0,0,0],[1,0,3,3],[3,0,3,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3],[1,0,0,0],[1,0,3,3],[3,0,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,2,3],[1,0,0,0],[1,0,3,3],[3,0,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3],[1,0,0,0],[1,0,3,3],[3,0,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2699,2746,2808] [2441,2503,2543,3050,3068,3152] :=
    ⟨Fin 4, «FinitePoly [[0,1,2,3],[1,0,0,0],[1,0,3,3],[3,0,3,0]]», by decideFin!⟩
