import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,6,7,0],[2,1,0,3,6,5,4,7],[7,0,1,2,3,4,5,6],[4,7,2,5,0,3,6,1],[5,6,7,0,1,2,3,4],[6,5,4,7,2,1,0,3],[3,4,5,6,7,0,1,2],[0,3,6,1,4,7,2,5]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,6,7,0],[2,1,0,3,6,5,4,7],[7,0,1,2,3,4,5,6],[4,7,2,5,0,3,6,1],[5,6,7,0,1,2,3,4],[6,5,4,7,2,1,0,3],[3,4,5,6,7,0,1,2],[0,3,6,1,4,7,2,5]]» : Magma (Fin 8) where
  op := memoFinOp fun x y => [[1,2,3,4,5,6,7,0],[2,1,0,3,6,5,4,7],[7,0,1,2,3,4,5,6],[4,7,2,5,0,3,6,1],[5,6,7,0,1,2,3,4],[6,5,4,7,2,1,0,3],[3,4,5,6,7,0,1,2],[0,3,6,1,4,7,2,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,6,7,0],[2,1,0,3,6,5,4,7],[7,0,1,2,3,4,5,6],[4,7,2,5,0,3,6,1],[5,6,7,0,1,2,3,4],[6,5,4,7,2,1,0,3],[3,4,5,6,7,0,1,2],[0,3,6,1,4,7,2,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1682] [411,614,1426,2035,2847,3659,4380] :=
    ⟨Fin 8, «FinitePoly [[1,2,3,4,5,6,7,0],[2,1,0,3,6,5,4,7],[7,0,1,2,3,4,5,6],[4,7,2,5,0,3,6,1],[5,6,7,0,1,2,3,4],[6,5,4,7,2,1,0,3],[3,4,5,6,7,0,1,2],[0,3,6,1,4,7,2,5]]», by decideFin!⟩
