
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,1],[1,1,1,1],[1,2,1,2],[1,3,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,3,1],[1,1,1,1],[1,2,1,2],[1,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,3,1],[1,1,1,1],[1,2,1,2],[1,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,3,1],[1,1,1,1],[1,2,1,2],[1,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [434] [427, 439, 854, 3318] :=
    ⟨Fin 4, «FinitePoly [[1,0,3,1],[1,1,1,1],[1,2,1,2],[1,3,3,1]]», by decideFin!⟩
