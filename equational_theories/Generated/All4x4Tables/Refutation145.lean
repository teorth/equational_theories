
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,3,3],[2,2,2,3],[0,0,0,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,3,3],[2,2,2,3],[0,0,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,3,3],[2,2,2,3],[0,0,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,3,3],[2,2,2,3],[0,0,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [257, 263] [2035, 2053, 2060, 2672, 2862, 2865, 2875, 3261, 3319, 3456] :=
    ⟨Fin 4, «FinitePoly [[1,1,3,3],[2,2,2,3],[0,0,0,3],[0,1,2,3]]», by decideFin!⟩
