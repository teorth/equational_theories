
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,5,0,3,4],[4,3,0,5,2,1],[3,4,1,2,5,0],[4,3,0,5,2,1],[5,0,3,4,1,2],[4,3,0,5,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,5,0,3,4],[4,3,0,5,2,1],[3,4,1,2,5,0],[4,3,0,5,2,1],[5,0,3,4,1,2],[4,3,0,5,2,1]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,5,0,3,4],[4,3,0,5,2,1],[3,4,1,2,5,0],[4,3,0,5,2,1],[5,0,3,4,1,2],[4,3,0,5,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,5,0,3,4],[4,3,0,5,2,1],[3,4,1,2,5,0],[4,3,0,5,2,1],[5,0,3,4,1,2],[4,3,0,5,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1543] [3862, 4065] :=
    ⟨Fin 6, «FinitePoly [[1,2,5,0,3,4],[4,3,0,5,2,1],[3,4,1,2,5,0],[4,3,0,5,2,1],[5,0,3,4,1,2],[4,3,0,5,2,1]]», by decideFin!⟩
