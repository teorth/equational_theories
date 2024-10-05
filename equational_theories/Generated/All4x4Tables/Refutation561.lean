
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,5,0,4,3,2],[2,5,0,4,1,3],[3,0,4,5,2,1],[1,4,5,0,3,2],[3,0,4,5,2,1],[2,4,5,0,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,5,0,4,3,2],[2,5,0,4,1,3],[3,0,4,5,2,1],[1,4,5,0,3,2],[3,0,4,5,2,1],[2,4,5,0,1,3]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,5,0,4,3,2],[2,5,0,4,1,3],[3,0,4,5,2,1],[1,4,5,0,3,2],[3,0,4,5,2,1],[2,4,5,0,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,5,0,4,3,2],[2,5,0,4,1,3],[3,0,4,5,2,1],[1,4,5,0,3,2],[3,0,4,5,2,1],[2,4,5,0,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1728] [1223, 1657, 3253] :=
    ⟨Fin 6, «FinitePoly [[1,5,0,4,3,2],[2,5,0,4,1,3],[3,0,4,5,2,1],[1,4,5,0,3,2],[3,0,4,5,2,1],[2,4,5,0,1,3]]», by decideFin!⟩
