import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,4,5,0],[4,1,2,5,0,3],[3,0,5,2,1,4],[0,5,4,3,2,1],[5,4,1,0,3,2],[2,3,0,1,4,5]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,4,5,0],[4,1,2,5,0,3],[3,0,5,2,1,4],[0,5,4,3,2,1],[5,4,1,0,3,2],[2,3,0,1,4,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[1,2,3,4,5,0],[4,1,2,5,0,3],[3,0,5,2,1,4],[0,5,4,3,2,1],[5,4,1,0,3,2],[2,3,0,1,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,4,5,0],[4,1,2,5,0,3],[3,0,5,2,1,4],[0,5,4,3,2,1],[5,4,1,0,3,2],[2,3,0,1,4,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [707,1316,2331,2940] [411,477,680,716,817,919,1020,1113,1426,1492,1519,1528,2441,2534,3050,4380,4435] :=
    ⟨Fin 6, «FinitePoly [[1,2,3,4,5,0],[4,1,2,5,0,3],[3,0,5,2,1,4],[0,5,4,3,2,1],[5,4,1,0,3,2],[2,3,0,1,4,5]]», by decideFin!⟩
