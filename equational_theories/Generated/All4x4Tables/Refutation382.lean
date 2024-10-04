
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,0,1],[1,2,1,1],[2,1,2,2],[3,2,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,0,1],[1,2,1,1],[2,1,2,2],[3,2,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,0,1],[1,2,1,1],[2,1,2,2],[3,2,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,0,1],[1,2,1,1],[2,1,2,2],[3,2,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [647, 1053] [417, 419, 427, 429, 620, 622, 630, 632, 655, 658, 825, 833, 1038, 1223, 1850, 4065, 4131] :=
    ⟨Fin 4, «FinitePoly [[0,2,0,1],[1,2,1,1],[2,1,2,2],[3,2,3,0]]», by decideFin!⟩
